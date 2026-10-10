import OAI.Combinatorics.HalvingLines.ZoomControl

namespace OAI

open Filter Topology

namespace PlanarHalving.Zoom
open Set Filter Metric
open scoped Topology

lemma equiv_opNorm_pos (A : Point ≃L[ℝ] Point) : 0<‖A.toContinuousLinearMap‖ := by
  apply norm_pos_iff.mpr
  intro he
  have ht : A (1,0)=0 := by
    have hh := congrArg (fun f : Point →L[ℝ] Point => f (1,0)) he
    exact hh
  have hz : ((1,0):Point)=0 := A.injective (ht.trans (map_zero A).symm)
  have h1 := congrArg Prod.fst hz
  norm_num at h1

noncomputable def normalizedLinear (A : Point ≃L[ℝ] Point) : Point →L[ℝ] Point :=
  ‖A.toContinuousLinearMap‖⁻¹ • A.toContinuousLinearMap

lemma normalizedLinear_norm (A : Point ≃L[ℝ] Point) : ‖normalizedLinear A‖=1 := by
  exact norm_smul_inv_norm (norm_pos_iff.mp (equiv_opNorm_pos A))

lemma unit_conorm_all (A : Point →L[ℝ] Point) (ε : ℝ)
    (h : ∀ x : Point, ‖x‖=1 → ε ≤ ‖A x‖) : ∀ x : Point, ε*‖x‖ ≤ ‖A x‖ := by
  intro x
  by_cases hx : x=0
  · simp [hx]
  · have hn : 0<‖x‖ := norm_pos_iff.mpr hx
    have he := h (‖x‖⁻¹ • x) (norm_smul_inv_norm hx)
    rw [map_smul,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn)] at he
    have ht := mul_le_mul_of_nonneg_left he hn.le
    calc
      ε*‖x‖ = ‖x‖*ε := mul_comm _ _
      _ ≤ ‖x‖*(‖x‖⁻¹*‖A x‖) := ht
      _ = ‖A x‖ := by rw [← mul_assoc,mul_inv_cancel₀ hn.ne',one_mul]

lemma normalizedLinear_subsequence (A : ℕ → Point ≃L[ℝ] Point) (ε : ℝ)
    (hε : 0<ε)
    (hbound : ∀ᶠ n in atTop, ∀ x : Point, ‖x‖=1 → ε ≤ ‖normalizedLinear (A n) x‖) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ L : Point →L[ℝ] Point,
      Tendsto (fun n => normalizedLinear (A (ρ n))) atTop (𝓝 L) ∧
      ‖L‖=1 ∧ Function.Injective L ∧ ∀ x : Point, ε*‖x‖ ≤ ‖L x‖ := by
  have hb (n : ℕ) : normalizedLinear (A n)∈closedBall (0:Point →L[ℝ] Point) 1 := by
    simp [normalizedLinear_norm]
  obtain ⟨L,_,ρ,hρ,hlim⟩ := (isCompact_closedBall (0:Point →L[ℝ] Point) 1).tendsto_subseq hb
  have hL : ‖L‖=1 := tendsto_nhds_unique hlim.norm
    (by simp only [Function.comp_def,normalizedLinear_norm]; exact tendsto_const_nhds)
  have hlower : ∀ x : Point, ε*‖x‖ ≤ ‖L x‖ := by
    apply unit_conorm_all
    intro x hx
    have ht : Tendsto (fun n => ‖normalizedLinear (A (ρ n)) x‖) atTop (𝓝 ‖L x‖) :=
      (((continuous_id.clm_apply (continuous_const : Continuous (fun _ : Point →L[ℝ] Point => x))).tendsto L).comp hlim).norm
    exact ge_of_tendsto ht ((hρ.tendsto_atTop.eventually hbound).mono fun _ hn => hn x hx)
  have hinj : Function.Injective L := by
    intro x y hxy
    have hb := hlower (x-y)
    rw [map_sub,hxy,sub_self,norm_zero] at hb
    have hn : ‖x-y‖=0 := by nlinarith [norm_nonneg (x-y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  exact ⟨ρ,hρ,L,hlim,hL,hinj,hlower⟩

lemma uniform_apply_linear_limit {X : Type*} (K : Set X)
    (f : ℕ → X → Point) (g : X → Point) (A : ℕ → Point →L[ℝ] Point)
    (L : Point →L[ℝ] Point) (hA : Tendsto A atTop (𝓝 L))
    (hnorm : ∀ n, ‖A n‖=1) (M : ℝ) (hM : 0≤M) (hg : ∀ x∈K, ‖g x‖≤M)
    (hf : TendstoUniformlyOn f g atTop K) :
    TendstoUniformlyOn (fun n x => A n (f n x)) (fun x => L (g x)) atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hδ : 0<ε/(2*(M+1)) := by positivity
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hf (ε/2) (by positivity),
    (Metric.tendsto_nhds.mp hA) _ hδ] with n hn hAn x hx
  have he : A n (f n x)-L (g x)=A n (f n x-g x)+(A n-L) (g x) := by
    simp only [map_sub,sub_apply]; abel
  have hdiff : ‖f n x-g x‖<ε/2 := by simpa only [dist_eq_norm,norm_sub_rev] using hn x hx
  have hAdiff : ‖A n-L‖<ε/(2*(M+1)) := by simpa only [dist_eq_norm] using hAn
  have hb := norm_add_le (A n (f n x-g x)) ((A n-L) (g x))
  have hfirst := (A n).le_opNorm (f n x-g x)
  rw [hnorm n,one_mul] at hfirst
  have hsecond := (A n-L).le_opNorm (g x)
  have hsmall : ‖A n-L‖*‖g x‖<ε/2 := by
    have hprod := mul_le_mul_of_nonneg_left (hg x hx) (norm_nonneg (A n-L))
    have hprod' : ‖A n-L‖*M < ε/2 := by
      have ht := (lt_div_iff₀ (by positivity : 0<2*(M+1))).mp hAdiff
      nlinarith [norm_nonneg (A n-L)]
    exact hprod.trans_lt hprod'
  rw [dist_eq_norm,norm_sub_rev,he]
  linarith

end PlanarHalving.Zoom

namespace PlanarHalving.Zoom
open Set Filter Metric
open scoped Topology

@[simp] lemma affineZoom_symm_apply (f : OpenPartialHomeomorph Point Point)
    (E B : Point ≃L[ℝ] Point) (p x₀ : Point) (q h : ℝ) (hq : q≠0) (hh : h≠0) (y : Point) :
    (affineZoom f E B p x₀ q h hq hh).symm y=
      E.symm (q⁻¹ • (f.symm (p+h • B.symm y)-x₀)) := rfl

lemma common_inverse_identity (f : OpenPartialHomeomorph Point Point)
    (E B G : Point ≃L[ℝ] Point) (p : Point) (q h : ℝ) (hq : q≠0) (hh : h≠0) (w : Point) :
    (q*‖(E.trans G).toContinuousLinearMap‖)⁻¹ •
      (G (f.symm (p+h • w))-G (f.symm p))=
      normalizedLinear (E.trans G)
        ((affineZoom f E B p (f.symm p) q h hq hh).symm (B w)) := by
  rw [affineZoom_symm_apply,B.symm_apply_apply]
  simp only [normalizedLinear,smul_apply,ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.trans_apply,E.apply_symm_apply,map_smul,map_sub,mul_inv_rev,smul_sub,smul_smul]
  congr 1 <;> congr 1 <;> ring

lemma uniform_common_inverse_limit (f : ℕ → OpenPartialHomeomorph Point Point)
    (E G : ℕ → Point ≃L[ℝ] Point) (B : Point ≃L[ℝ] Point) (p : Point)
    (q h : ℕ → ℝ) (hq : ∀ n, q n≠0) (hh : ∀ n, h n≠0) (sgn : ℝ)
    (L : Point →L[ℝ] Point)
    (hL : Tendsto (fun n => normalizedLinear ((E n).trans (G n))) atTop (𝓝 L))
    (hinv : ∀ K : Set Point, IsCompact K → TendstoUniformlyOn
      (fun n => (affineZoom (f n) (E n) B p ((f n).symm p) (q n) (h n) (hq n) (hh n)).symm)
      (fun x => sgn • x) atTop K) :
    ∀ K : Set Point, IsCompact K → TendstoUniformlyOn
      (fun n w => (q n*‖((E n).trans (G n)).toContinuousLinearMap‖)⁻¹ •
        (G n ((f n).symm (p+h n • w))-G n ((f n).symm p)))
      (fun w => L (sgn • B w)) atTop K := by
  intro K hK
  let g : Point → Point := fun w => sgn • B w
  have hg : Continuous g := by
    dsimp [g]
    exact (continuous_const : Continuous (fun _ : Point => sgn)).smul B.continuous
  obtain ⟨R,hR⟩ := (Metric.isBounded_iff_subset_closedBall (0:Point)).mp (hK.image hg).isBounded
  have hgb (x : Point) (hx : x∈K) : ‖g x‖ ≤ max R 0 := by
    apply le_trans _ (le_max_left _ _)
    simpa only [mem_closedBall,dist_zero_right] using hR (mem_image_of_mem g hx)
  have hf : TendstoUniformlyOn
      (fun n w => (affineZoom (f n) (E n) B p ((f n).symm p) (q n) (h n) (hq n) (hh n)).symm (B w))
      g atTop K := by
    exact ((hinv (B '' K) (hK.image B.continuous)).comp B).mono
      (by intro x hx; exact mem_image_of_mem B hx)
  have ht := uniform_apply_linear_limit K _ g
    (fun n => normalizedLinear ((E n).trans (G n))) L hL
    (fun n => normalizedLinear_norm _) (max R 0) (le_max_right _ _) hgb hf
  simpa only [← common_inverse_identity] using ht

end PlanarHalving.Zoom

namespace PlanarHalving.Zoom
open Set Filter Metric
open scoped Topology

lemma common_frame_condition (B : Point ≃L[ℝ] Point)
    (S : Fin 3 → Set ℝ) (hS : ∀ i, IsClosed (S i))
    (hSb : ∀ i, S i ⊆ Icc (0:ℝ) 1) (hdis : ∀ i j, i≠j → Disjoint (S i) (S j))
    (v : Fin 3 → Point) (hv : ∀ i j, i≠j → detPair (v i) (v j) ≠ 0) :
    ∃ ε : ℝ, 0<ε ∧ ∀ (A : ℕ → Point ≃L[ℝ] Point) (u : ℕ → Fin 3 → Point),
      (∀ n i, ‖u n i‖=1) →
      (∀ ρ : ℕ → ℕ, StrictMono ρ → ∀ x : Fin 3 → Point,
        Tendsto (u ∘ ρ) atTop (𝓝 x) →
        ∀ i, ∃ z∈S i, detPair (x i) (B (RankLimits.reflectFirst (Directions.simplex z)))=0) →
      (∀ n i, detPair (A n (u n i)) (v i)=0) →
      ∀ᶠ n in atTop, ∀ x : Point, ‖x‖=1 → ε ≤ ‖normalizedLinear (A n) x‖ := by
  obtain ⟨δ,hδ,hsep⟩ := eventually_separated_of_allowed_clusters B S hS hSb hdis
  obtain ⟨ε,hε,hcond⟩ := three_lines_uniform_conorm v hv δ hδ
  refine ⟨ε,hε,?_⟩
  intro A u hu hcluster hline
  filter_upwards [hsep u hu hcluster] with n hn
  apply hcond (normalizedLinear (A n)) (normalizedLinear_norm _) (u n) (hu n) hn
  intro i
  change detPair (‖(A n).toContinuousLinearMap‖⁻¹ • A n (u n i)) (v i)=0
  have he : detPair (‖(A n).toContinuousLinearMap‖⁻¹ • A n (u n i)) (v i)=
      ‖(A n).toContinuousLinearMap‖⁻¹*detPair (A n (u n i)) (v i) := by dsimp [detPair]; ring
  rw [he,hline,mul_zero]

end PlanarHalving.Zoom

namespace PlanarHalving.Zoom
open Set Filter Metric
open scoped Topology

def RadialCompare (f : Point → Point) (p : Point) (h C T : ℝ) : Prop :=
  (∀ u v : Point, ‖u-p‖=h/T → ‖v-p‖=h →
    ‖f v-f p‖ ≤ C*T*‖f u-f p‖) ∧
  (∀ u v : Point, ‖u-p‖=h/T → ‖v-p‖=h →
    T*‖f u-f p‖ ≤ C*‖f v-f p‖)

lemma uniform_radial_compare (f : ℕ → Point → Point) (L : Point →L[ℝ] Point)
    (l u C T : ℝ) (hl : 0<l) (hu : 0≤u) (hT : 1≤T) (hC : u<C*l)
    (hlower : ∀ x : Point, l*‖x‖ ≤ ‖L x‖) (hupper : ∀ x : Point, ‖L x‖ ≤ u*‖x‖)
    (hf : TendstoUniformlyOn f L atTop (closedBall 0 1)) :
    ∀ᶠ n in atTop, ∀ x y : Point, ‖x‖=1/T → ‖y‖=1 →
      ‖f n y‖ ≤ C*T*‖f n x‖ ∧ T*‖f n x‖ ≤ C*‖f n y‖ := by
  have hTp : 0<T := lt_of_lt_of_le zero_lt_one hT
  have hCp : 0<C := by nlinarith
  let ε := (C*l-u)/(2*(C*T+T+C+1))
  have hε : 0<ε := by dsimp [ε]; positivity
  have hεeq : ε*(2*(C*T+T+C+1))=C*l-u := by
    dsimp [ε]
    exact div_mul_cancel₀ _ (by positivity)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hf ε hε] with n hn x y hx hy
  have hxball : x∈closedBall (0:Point) 1 := by
    rw [mem_closedBall_zero_iff,hx]
    exact (div_le_one hTp).mpr hT
  have hyball : y∈closedBall (0:Point) 1 := by simp [hy]
  have hxe : |‖f n x‖-‖L x‖|<ε := by
    exact (abs_norm_sub_norm_le _ _).trans_lt (by simpa only [dist_eq_norm,norm_sub_rev] using hn x hxball)
  have hye : |‖f n y‖-‖L y‖|<ε := by
    exact (abs_norm_sub_norm_le _ _).trans_lt (by simpa only [dist_eq_norm,norm_sub_rev] using hn y hyball)
  have hxl := hlower x; have hxu := hupper x
  have hyl := hlower y; have hyu := hupper y
  rw [hx] at hxl hxu; rw [hy,mul_one] at hyl hyu
  have hxlo : l/T-ε ≤ ‖f n x‖ := by
    have hh := (abs_lt.mp hxe).1
    have he : l*(1/T)=l/T := by ring
    rw [he] at hxl
    linarith
  have hxhi : ‖f n x‖ ≤ u/T+ε := by
    have hh := (abs_lt.mp hxe).2
    have he : u*(1/T)=u/T := by ring
    rw [he] at hxu
    linarith
  have hylo : l-ε ≤ ‖f n y‖ := by linarith [(abs_lt.mp hye).1]
  have hyhi : ‖f n y‖ ≤ u+ε := by linarith [(abs_lt.mp hye).2]
  have hxeq : T*(l/T)=l := mul_div_cancel₀ l hTp.ne'
  have hxueq : T*(u/T)=u := mul_div_cancel₀ u hTp.ne'
  constructor
  · have hm := mul_le_mul_of_nonneg_left hxlo (mul_pos hCp hTp).le
    have he : C*T*(l/T-ε)=C*l-C*T*ε := by rw [mul_sub,mul_assoc C T (l/T),hxeq]
    rw [he] at hm
    have hp : 0≤ε*(T+C+1) := by positivity
    nlinarith
  · have hm := mul_le_mul_of_nonneg_left hylo hCp.le
    have hx' := mul_le_mul_of_nonneg_left hxhi hTp.le
    rw [mul_add,hxueq] at hx'
    have hp : 0≤ε*(C*T+1) := by positivity
    nlinarith

lemma radial_compare_of_zoom (f : Point → Point) (p : Point) (h s C T : ℝ)
    (hh : 0<h) (hs : 0<s)
    (H : ∀ x y : Point, ‖x‖=1/T → ‖y‖=1 →
      ‖s • (f (p+h • y)-f p)‖ ≤ C*T*‖s • (f (p+h • x)-f p)‖ ∧
      T*‖s • (f (p+h • x)-f p)‖ ≤ C*‖s • (f (p+h • y)-f p)‖) :
    RadialCompare f p h C T := by
  have hrepr (z : Point) : p+h • (h⁻¹ • (z-p))=z := by
    rw [smul_smul,mul_inv_cancel₀ hh.ne',one_smul]; abel
  have hx (z : Point) (hz : ‖z-p‖=h/T) : ‖h⁻¹ • (z-p)‖=1/T := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hh),hz]
    field_simp
  have hy (z : Point) (hz : ‖z-p‖=h) : ‖h⁻¹ • (z-p)‖=1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hh),hz,inv_mul_cancel₀ hh.ne']
  constructor
  · intro u v hu hv
    have he := (H (h⁻¹ • (u-p)) (h⁻¹ • (v-p)) (hx u hu) (hy v hv)).1
    simp only [hrepr,norm_smul,Real.norm_eq_abs,abs_of_pos hs] at he
    nlinarith
  · intro u v hu hv
    have he := (H (h⁻¹ • (u-p)) (h⁻¹ • (v-p)) (hx u hu) (hy v hv)).2
    simp only [hrepr,norm_smul,Real.norm_eq_abs,abs_of_pos hs] at he
    nlinarith

end PlanarHalving.Zoom

namespace PlanarHalving.Directions
open Set
lemma allowed_closed {ι : Type*} (Q : Plane ≃L[ℝ] Plane) (g : ι → Plane →L[ℝ] ℝ)
    (lo hi : ι → ℝ) (t : ℝ) : IsClosed (allowed Q g lo hi t) := by
  have hc (i : ι) : Continuous (fun x : ℝ => g i (Q (simplex x))) :=
    (g i).continuous.comp (Q.continuous.comp (continuous_id.prodMk (continuous_const.sub continuous_id)))
  have he : allowed Q g lo hi t = Icc (0:ℝ) 1 ∩
      ⋂ i, {x : ℝ | (hi i<t → 0≤g i (Q (simplex x))) ∧ (t<lo i → g i (Q (simplex x))≤0)} := by
    ext x; simp only [allowed,mem_ofPred_eq,mem_inter_iff,mem_iInter]
  rw [he]
  apply isClosed_Icc.inter (isClosed_iInter fun i => ?_)
  change IsClosed ({x : ℝ | hi i<t → 0≤g i (Q (simplex x))} ∩
    {x : ℝ | t<lo i → g i (Q (simplex x))≤0})
  apply IsClosed.inter
  · by_cases h : hi i<t
    · simpa only [h,true_implies] using isClosed_le continuous_const (hc i)
    · simpa only [h,false_implies,ofPred_true] using (isClosed_univ : IsClosed (univ:Set ℝ))
  · by_cases h : t<lo i
    · simpa only [h,true_implies] using isClosed_le (hc i) continuous_const
    · simpa only [h,false_implies,ofPred_true] using (isClosed_univ : IsClosed (univ:Set ℝ))
end PlanarHalving.Directions

namespace PlanarHalving.Zoom
open Set Filter Metric
open scoped Topology

def FrameCondition (B : Point ≃L[ℝ] Point) (S : Fin 3 → Set ℝ)
    (v : Fin 3 → Point) (ε : ℝ) : Prop :=
  ∀ (A : ℕ → Point ≃L[ℝ] Point) (u : ℕ → Fin 3 → Point),
    (∀ n i, ‖u n i‖=1) →
    (∀ ρ : ℕ → ℕ, StrictMono ρ → ∀ x : Fin 3 → Point,
      Tendsto (u ∘ ρ) atTop (𝓝 x) →
      ∀ i, ∃ z∈S i, detPair (x i) (B (RankLimits.reflectFirst (Directions.simplex z)))=0) →
    (∀ n i, detPair (A n (u n i)) (v i)=0) →
    ∀ᶠ n in atTop, ∀ x : Point, ‖x‖=1 → ε ≤ ‖normalizedLinear (A n) x‖

lemma exists_frameCondition (B : Point ≃L[ℝ] Point)
    (S : Fin 3 → Set ℝ) (hS : ∀ i, IsClosed (S i))
    (hSb : ∀ i, S i ⊆ Icc (0:ℝ) 1) (hdis : ∀ i j, i≠j → Disjoint (S i) (S j))
    (v : Fin 3 → Point) (hv : ∀ i j, i≠j → detPair (v i) (v j) ≠ 0) :
    ∃ ε : ℝ, 0<ε ∧ FrameCondition B S v ε :=
  common_frame_condition B S hS hSb hdis v hv

lemma common_limit_bounds (B : Point ≃L[ℝ] Point) (L : Point →L[ℝ] Point)
    (ε sgn : ℝ) (hε : 0<ε) (hsgn : sgn=1 ∨ sgn=-1) (hL : ‖L‖=1)
    (hlower : ∀ x : Point, ε*‖x‖ ≤ ‖L x‖) :
    let M := L.comp (sgn • B.toContinuousLinearMap)
    (∀ x : Point, (ε/‖B.symm.toContinuousLinearMap‖)*‖x‖ ≤ ‖M x‖) ∧
    (∀ x : Point, ‖M x‖ ≤ ‖B.toContinuousLinearMap‖*‖x‖) := by
  have habs : |sgn|=1 := by rcases hsgn with rfl | rfl <;> norm_num
  have hn (x : Point) : ‖sgn • B x‖=‖B x‖ := by rw [norm_smul,Real.norm_eq_abs,habs,one_mul]
  constructor
  · intro x
    have hb := B.symm.toContinuousLinearMap.le_opNorm (B x)
    simp only [ContinuousLinearEquiv.coe_coe,B.symm_apply_apply] at hb
    have he := hlower (sgn • B x)
    rw [hn] at he
    change _ ≤ ‖L (sgn • B x)‖
    have hp := equiv_opNorm_pos B.symm
    have hd : ‖x‖/‖B.symm.toContinuousLinearMap‖ ≤ ‖B x‖ := (div_le_iff₀ hp).mpr (by nlinarith)
    have hm := mul_le_mul_of_nonneg_left hd hε.le
    have hid : ε*(‖x‖/‖B.symm.toContinuousLinearMap‖)=
        ε/‖B.symm.toContinuousLinearMap‖*‖x‖ := by ring
    rw [hid] at hm
    exact hm.trans he
  · intro x
    have he := L.le_opNorm (sgn • B x)
    rw [hL,one_mul,hn] at he
    exact he.trans (B.toContinuousLinearMap.le_opNorm x)

end PlanarHalving.Zoom

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows RankCoordinates Zoom
open scoped Topology unitInterval

lemma actual_common_inverse_limit {ι : Type*} (F : ℕ → Configuration) {A B : Window}
    (hAB : Before A B) (hA : ∀ n, 0 < length (F n).R A)
    (hB : ∀ n, 0 < length (F n).R B) (C : ι → Window)
    (hCB : ∀ i, Before (C i) A ∧ Before (C i) B)
    (hC : ∀ i, ∀ᶠ n in atTop, 0 < length (F n).R (C i))
    (D : ι → Point →L[ℝ] ℝ) (c : ι → ℝ) (p : Point)
    (hp : p ∈ Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0)
    (h q : ℕ → ℝ) (hh : ∀ n, 0<h n) (hq : ∀ n, 0<q n)
    (E G : ℕ → Point ≃L[ℝ] Point) (B' : Point ≃L[ℝ] Point)
    (t : Fin 3 → I) (htA : ∀ i, t i ≤ lower A) (htB : ∀ i, t i ≤ lower B)
    (v : Fin 3 → Point) (ε : ℝ) (hε : 0<ε)
    (hcond : FrameCondition B'
      (fun j => Directions.allowed reflectFirst D (fun i => (lower (C i):ℝ))
        (fun i => (upper (C i):ℝ)) (t j)) v ε)
    (hG : ∀ n i, detPair (G n (1,(F n).timeSlope (t i))) (v i)=0)
    (sgn : ℝ) (hsgn : sgn=1 ∨ sgn=-1)
    (hj : ∀ i R, 0 ≤ R → TendstoUniformlyOn
      (fun n u => (((F n).extendedRank true A B (C i) (p+h n • u) : ℝ)-c i)/h n)
      (D i) atTop (closedBall 0 R))
    (hunif : ∀ K : Set Point, IsCompact K → TendstoUniformlyOn
      (fun n => affineZoom ((F n).rankChart hAB (hA n) (hB n)) (E n) B' p
        (((F n).rankChart hAB (hA n) (hB n)).symm p) (q n) (h n) (hq n).ne' (hh n).ne')
      (fun x => sgn • x) atTop K)
    (hinv : ∀ K : Set Point, IsCompact K → TendstoUniformlyOn
      (fun n => (affineZoom ((F n).rankChart hAB (hA n) (hB n)) (E n) B' p
        (((F n).rankChart hAB (hA n) (hB n)).symm p) (q n) (h n) (hq n).ne' (hh n).ne').symm)
      (fun x => sgn • x) atTop K) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ r : ℕ → ℝ, (∀ n, 0<r n) ∧
      ∃ M : Point →L[ℝ] Point,
      (∀ x : Point, (ε/‖B'.symm.toContinuousLinearMap‖)*‖x‖ ≤ ‖M x‖) ∧
      (∀ x : Point, ‖M x‖ ≤ ‖B'.toContinuousLinearMap‖*‖x‖) ∧
      ∀ K : Set Point, IsCompact K → TendstoUniformlyOn
        (fun n w => r n • (G (ρ n) (((F (ρ n)).rankChart hAB (hA (ρ n)) (hB (ρ n))).symm
          (p+h (ρ n) • w))-G (ρ n) (((F (ρ n)).rankChart hAB (hA (ρ n)) (hB (ρ n))).symm p)))
        M atTop K := by
  let u := fun n i => forwardUnit (F n) (E n) (t i)
  let A' := fun n => (E n).trans (G n)
  have hbound : ∀ᶠ n in atTop, ∀ x : Point, ‖x‖=1 → ε ≤ ‖normalizedLinear (A' n) x‖ := by
    apply hcond A' u (fun n i => forwardUnit_norm _ _ _)
    · intro ρ hρ x hx i
      exact actual_forwardUnit_clusters F hAB hA hB C hCB hC D c p hp h q hh hq E B'
        (t i) (htA i) (htB i) sgn hsgn hj (hunif _ (isCompact_closedBall _ _))
        ρ hρ (x i) (tendsto_pi_nhds.mp hx i)
    · intro n i
      change detPair (G n (E n (forwardUnit (F n) (E n) (t i)))) (v i)=0
      rw [forwardUnit_map,map_smul]
      have he : detPair (‖(E n).symm (1,(F n).timeSlope (t i))‖⁻¹ • G n (1,(F n).timeSlope (t i))) (v i)=
          ‖(E n).symm (1,(F n).timeSlope (t i))‖⁻¹*detPair (G n (1,(F n).timeSlope (t i))) (v i) := by
        dsimp [detPair]; ring
      rw [he,hG,mul_zero]
  obtain ⟨ρ,hρ,L,hL,hLn,_,hLl⟩ := normalizedLinear_subsequence A' ε hε hbound
  let M := L.comp (sgn • B'.toContinuousLinearMap)
  let r := fun n => (q (ρ n)*‖(A' (ρ n)).toContinuousLinearMap‖)⁻¹
  have hr (n : ℕ) : 0<r n := inv_pos.mpr (mul_pos (hq _) (equiv_opNorm_pos _))
  obtain ⟨hMl,hMu⟩ := common_limit_bounds B' L ε sgn hε hsgn hLn hLl
  refine ⟨ρ,hρ,r,hr,M,hMl,hMu,?_⟩
  intro K hK
  exact uniform_common_inverse_limit
    (fun n => (F (ρ n)).rankChart hAB (hA (ρ n)) (hB (ρ n)))
    (E ∘ ρ) (G ∘ ρ) B' p (q ∘ ρ) (h ∘ ρ)
    (fun n => (hq _).ne') (fun n => (hh _).ne') sgn L hL
    (fun K hK => (hinv K hK).seq_tendstoUniformlyOn ρ hρ.tendsto_atTop) K hK

end PlanarHalving.RankLimits

end OAI
