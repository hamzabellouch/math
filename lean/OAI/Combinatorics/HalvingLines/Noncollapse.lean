import OAI.Combinatorics.HalvingLines.Foliations

namespace OAI

open Filter Topology

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows RankCoordinates Zoom
open scoped Topology unitInterval

lemma diagonal_common_limit {ι : Type*} (F : ℕ → Configuration) {A B : Window}
    (hAB : Before A B) (hA : ∀ n, 0 < length (F n).R A)
    (hB : ∀ n, 0 < length (F n).R B) (C : ι → Window)
    (hCB : ∀ i, Before (C i) A ∧ Before (C i) B)
    (hC : ∀ i, ∀ᶠ n in atTop, 0 < length (F n).R (C i))
    (D : ι → Point →L[ℝ] ℝ) (c : ι → ℝ) (p : Point)
    (hp : p ∈ Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0)
    (h : ℕ → ℝ) (hh : ∀ n, 0<h n) (hlim : Tendsto h atTop (𝓝 0))
    (hj : ∀ i R, 0 ≤ R → TendstoUniformlyOn
      (fun n u => (((F n).extendedRank true A B (C i) (p+h n • u) : ℝ)-c i)/h n)
      (D i) atTop (closedBall 0 R))
    (τ₁ τ₂ τ₃ : I) (hτA : ∀ i, foliationTriple τ₁ τ₂ τ₃ i ≤ lower A)
    (hτB : ∀ i, foliationTriple τ₁ τ₂ τ₃ i ≤ lower B)
    (h12 : ∀ n, (F n).timeSlope τ₁ < (F n).timeSlope τ₂)
    (h23 : ∀ n, (F n).timeSlope τ₂ < (F n).timeSlope τ₃)
    (z : Foliation → ℝ)
    (hz : ∀ j, Directions.allowed reflectFirst D (fun i => (lower (C i):ℝ))
      (fun i => (upper (C i):ℝ)) ((foliationTriple τ₁ τ₂ τ₃ j : I) : ℝ)={z j})
    (B' : Point ≃L[ℝ] Point) (d : Foliation → ℝ)
    (hB' : ∀ i, B' (reflectFirst (Directions.simplex (z i)))=d i • i.direction)
    (hball : ∀ n, closedBall (0:Point) 1 ⊆ {w | p+h n • B'.symm w∈Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0})
    (G : ℕ → Point ≃L[ℝ] Point) (t : Fin 3 → I)
    (htA : ∀ i, t i ≤ lower A) (htB : ∀ i, t i ≤ lower B)
    (v : Fin 3 → Point) (ε : ℝ) (hε : 0<ε)
    (hcond : FrameCondition B'
      (fun j => Directions.allowed reflectFirst D (fun i => (lower (C i):ℝ))
        (fun i => (upper (C i):ℝ)) (t j)) v ε)
    (hG : ∀ n i, detPair (G n (1,(F n).timeSlope (t i))) (v i)=0) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ r : ℕ → ℝ, (∀ n, 0<r n) ∧
      ∃ M : Point →L[ℝ] Point,
      (∀ x : Point, (ε/‖B'.symm.toContinuousLinearMap‖)*‖x‖ ≤ ‖M x‖) ∧
      (∀ x : Point, ‖M x‖ ≤ ‖B'.toContinuousLinearMap‖*‖x‖) ∧
      ∀ K : Set Point, IsCompact K → TendstoUniformlyOn
        (fun n w => r n • (G (ρ n) (((F (ρ n)).rankChart hAB (hA (ρ n)) (hB (ρ n))).symm
          (p+h (ρ n) • w))-G (ρ n) (((F (ρ n)).rankChart hAB (hA (ρ n)) (hB (ρ n))).symm p)))
        M atTop K := by
  obtain ⟨E,s,hs,hE⟩ := positive_slope_frames F τ₁ τ₂ τ₃ h12 h23
  have hex (n : ℕ) : ∃ q : ℝ, ∃ hq : 0<q,
      ‖affineZoom ((F n).rankChart hAB (hA n) (hB n)) (E n) B' p
        (((F n).rankChart hAB (hA n) (hB n)).symm p) q (h n) hq.ne' (hh n).ne' (1,0)‖=1 := by
    apply affineZoom_normalizing_scale _ ((F n).rankChart_source hAB (hA n) (hB n))
      (E n) B' (by rw [(F n).rankChart_target]; exact hp) (h n) (hh n).ne'
    simpa only [(F n).rankChart_target] using hball n
  choose q hq hone using hex
  obtain ⟨ρ,hρ,sgn,hsgn,hu,hi⟩ := actual_zoom_compactness F hAB hA hB C hCB hC D c p hp
    h q hh hq hlim E B' (foliationTriple τ₁ τ₂ τ₃) hτA hτB z hz s
    (fun n i => (hs n i).le) d hE hB' hj hone
  obtain ⟨ψ,hψ,r,hr,M,hMl,hMu,hM⟩ := actual_common_inverse_limit (F ∘ ρ) hAB
    (fun n => hA (ρ n)) (fun n => hB (ρ n)) C hCB
    (fun i => hρ.tendsto_atTop.eventually (hC i)) D c p hp (h ∘ ρ) (q ∘ ρ)
    (fun n => hh (ρ n)) (fun n => hq (ρ n)) (E ∘ ρ) (G ∘ ρ) B' t htA htB v ε hε hcond
    (fun n i => hG (ρ n) i) sgn hsgn
    (fun i R hR => (hj i R hR).seq_tendstoUniformlyOn ρ hρ.tendsto_atTop) hu hi
  exact ⟨ρ ∘ ψ,hρ.comp hψ,r,hr,M,hMl,hMu,hM⟩

end PlanarHalving.RankLimits

namespace PlanarHalving.Zoom
open Set Filter Metric
open scoped Topology

lemma compact_scaling_eventually (U : Set Point) (hU : IsOpen U) {p : Point} (hp : p∈U)
    (B : Point ≃L[ℝ] Point) (h : ℕ → ℝ) (hlim : Tendsto h atTop (𝓝 0))
    (K : Set Point) (hK : IsCompact K) :
    ∀ᶠ n in atTop, ∀ w∈K, p+h n • B w∈U := by
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp)
  obtain ⟨R,hR⟩ := (Metric.isBounded_iff_subset_closedBall (0:Point)).mp (hK.image B.continuous).isBounded
  have ht : Tendsto (fun n => |h n| *max R 0) atTop (𝓝 0) := by simpa using hlim.abs.mul_const (max R 0)
  filter_upwards [ht.eventually (gt_mem_nhds hr)] with n hn w hw
  apply hrsub
  rw [mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs]
  have hw' : ‖B w‖ ≤ max R 0 := by
    apply le_trans _ (le_max_left _ _)
    simpa only [mem_closedBall,dist_zero_right] using hR (mem_image_of_mem B hw)
  exact (mul_le_mul_of_nonneg_left hw' (abs_nonneg _)).trans_lt hn

lemma radial_of_jet_diagonals {ι : Type*} [Nonempty ι] [Countable ι]
    (f : ℕ → ι → Point → ℝ) (c : ι → ℝ) (D : ι → Point →L[ℝ] ℝ)
    (L : ℕ → Point → Point) (p : Point) (l u C : ℝ)
    (hl : 0<l) (hu : 0≤u) (hC : u<C*l)
    (hfirst : ∀ i R, 0 ≤ R → ∀ ε > 0, ∀ᶠ h in 𝓝[>] (0:ℝ), ∀ᶠ n in atTop,
      ∀ x ∈ closedBall p (R*h), dist (f n i x) (c i+D i (x-p)) < ε*h)
    (hdiag : ∀ (h : ℕ → ℝ) (N : ℕ → ℕ), (∀ m, 0<h m) → Tendsto h atTop (𝓝 0) →
      Tendsto N atTop atTop →
      (∀ i R, 0 ≤ R → TendstoUniformlyOn
        (fun m w => (f (N m) i (p+h m • w)-c i)/h m) (D i) atTop (closedBall 0 R)) →
      ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ r : ℕ → ℝ, (∀ n, 0<r n) ∧
        ∃ M : Point →L[ℝ] Point, (∀ x : Point, l*‖x‖ ≤ ‖M x‖) ∧
        (∀ x : Point, ‖M x‖ ≤ u*‖x‖) ∧
        TendstoUniformlyOn
          (fun n w => r n • (L (N (ρ n)) (p+h (ρ n) • w)-L (N (ρ n)) p))
          M atTop (closedBall 0 1)) :
    ∀ T : ℝ, 1≤T → ∀ᶠ h in 𝓝[>] (0:ℝ), ∀ᶠ n in atTop,
      RadialCompare (L n) p h C T := by
  intro T hT
  by_contra hbad
  have hf : ∃ᶠ h in 𝓝[>] (0:ℝ), ∃ᶠ n in atTop, ¬RadialCompare (L n) p h C T := by
    simpa only [Filter.Frequently,not_not] using hbad
  obtain ⟨h,N,hh,hlim,hN,hbad,hj⟩ := RankLimit.jet_diagonal f c D p hfirst
    (fun h n => ¬RadialCompare (L n) p h C T) hf
  obtain ⟨ρ,hρ,r,hr,M,hMl,hMu,hconv⟩ := hdiag h N hh hlim hN hj
  have hc := uniform_radial_compare _ M l u C T hl hu hT hC hMl hMu hconv
  obtain ⟨n,hn⟩ := hc.exists
  exact hbad (ρ n) (radial_compare_of_zoom (L (N (ρ n))) p (h (ρ n)) (r n) C T
    (hh _) (hr _) hn)

end PlanarHalving.Zoom

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows RankCoordinates Zoom
open scoped Topology unitInterval

lemma actual_radial_comparison {ι : Type*} [Nonempty ι] [Countable ι]
    (F : ℕ → Configuration) (hR : Tendsto (fun n => (F n).R) atTop atTop) {A B : Window}
    (hAB : Before A B) (hA : ∀ n, 0 < length (F n).R A)
    (hB : ∀ n, 0 < length (F n).R B) (C : ι → Window)
    (hCB : ∀ i, Before (C i) A ∧ Before (C i) B)
    (hC : ∀ i, ∀ᶠ n in atTop, 0 < length (F n).R (C i))
    (D : ι → Point →L[ℝ] ℝ) (c : ι → ℝ) (p : Point)
    (hp : p ∈ Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0)
    (hfirst : ∀ i R, 0 ≤ R → ∀ ε > 0, ∀ᶠ h in 𝓝[>] (0:ℝ), ∀ᶠ n in atTop,
      ∀ x ∈ closedBall p (R*h),
        dist (((F n).extendedRank true A B (C i) x : ℝ)) (c i+D i (x-p)) < ε*h)
    (τ₁ τ₂ τ₃ : I) (hτ12 : τ₁<τ₂) (hτ23 : τ₂<τ₃)
    (hτA : ∀ i, foliationTriple τ₁ τ₂ τ₃ i ≤ lower A)
    (hτB : ∀ i, foliationTriple τ₁ τ₂ τ₃ i ≤ lower B)
    (z : Foliation → ℝ)
    (hz : ∀ j, Directions.allowed reflectFirst D (fun i => (lower (C i):ℝ))
      (fun i => (upper (C i):ℝ)) ((foliationTriple τ₁ τ₂ τ₃ j : I) : ℝ)={z j})
    (B' : Point ≃L[ℝ] Point) (d : Foliation → ℝ)
    (hB' : ∀ i, B' (reflectFirst (Directions.simplex (z i)))=d i • i.direction)
    (G : ℕ → Point ≃L[ℝ] Point) (t : Fin 3 → I)
    (htA : ∀ i, t i ≤ lower A) (htB : ∀ i, t i ≤ lower B)
    (v : Fin 3 → Point) (ε : ℝ) (hε : 0<ε)
    (hcond : FrameCondition B'
      (fun j => Directions.allowed reflectFirst D (fun i => (lower (C i):ℝ))
        (fun i => (upper (C i):ℝ)) (t j)) v ε)
    (hG : ∀ n i, detPair (G n (1,(F n).timeSlope (t i))) (v i)=0)
    (C₀ : ℝ) (hC₀ : ‖B'.toContinuousLinearMap‖ < C₀*(ε/‖B'.symm.toContinuousLinearMap‖)) :
    ∀ T : ℝ, 1≤T → ∀ᶠ h in 𝓝[>] (0:ℝ), ∀ᶠ n in atTop,
      RadialCompare (fun x => G n (((F n).rankChart hAB (hA n) (hB n)).symm x)) p h C₀ T := by
  apply radial_of_jet_diagonals
    (fun n i x => ((F n).extendedRank true A B (C i) x : ℝ)) c D
    (fun n x => G n (((F n).rankChart hAB (hA n) (hB n)).symm x)) p
    (ε/‖B'.symm.toContinuousLinearMap‖) ‖B'.toContinuousLinearMap‖ C₀
    (div_pos hε (equiv_opNorm_pos _)) (norm_nonneg _) hC₀ hfirst
  intro h N hh hlim hN hj
  have h12 := timeSlope_eventually_lt (F ∘ N) (hR.comp hN) hτ12
  have h23 := timeSlope_eventually_lt (F ∘ N) (hR.comp hN) hτ23
  have hball := compact_scaling_eventually _ (isOpen_Ioo.prod isOpen_Ioo) hp B'.symm h hlim
    (closedBall 0 1) (isCompact_closedBall _ _)
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp (h12.and (h23.and hball))
  let η : ℕ → ℕ := fun n => n+n₀
  have hη : StrictMono η := by intro a b hab; dsimp [η]; omega
  have hgood (n : ℕ) := hn₀ (η n) (by dsimp [η]; omega)
  obtain ⟨ρ,hρ,r,hr,M,hMl,hMu,hconv⟩ := diagonal_common_limit (F ∘ N ∘ η) hAB
    (fun n => hA (N (η n))) (fun n => hB (N (η n))) C hCB
    (fun i => (hN.comp hη.tendsto_atTop).eventually (hC i)) D c p hp (h ∘ η)
    (fun n => hh (η n)) (hlim.comp hη.tendsto_atTop)
    (fun i R hR => (hj i R hR).seq_tendstoUniformlyOn η hη.tendsto_atTop)
    τ₁ τ₂ τ₃ hτA hτB (fun n => (hgood n).1) (fun n => (hgood n).2.1)
    z hz B' d hB' (fun n => (hgood n).2.2) (G ∘ N ∘ η) t htA htB v ε hε hcond
    (fun n i => hG (N (η n)) i)
  exact ⟨η ∘ ρ,hη.comp hρ,r,hr,M,hMl,hMu,hconv _ (isCompact_closedBall _ _)⟩

end PlanarHalving.RankLimits

namespace PlanarHalving.Spatial
open Set Filter Metric
open scoped Topology

lemma ray_image_leaves_compact (f : OpenPartialHomeomorph Point Point)
    (hs : f.source=univ) (K : Set Point) (hK : IsCompact K) (hKt : K ⊆ f.target)
    (x v : Point) (hv : v≠0) : ∃ t : ℝ, 0≤t ∧ f (x+t • v) ∉ K := by
  have hc := hK.image_of_continuousOn (f.continuousOn_symm.mono hKt)
  obtain ⟨C,hC,hbound⟩ := hc.isBounded.exists_pos_norm_le
  have hvp := norm_pos_iff.mpr hv
  let t : ℝ := (C+‖x‖+1)/‖v‖
  have ht : 0≤t := by dsimp [t]; positivity
  refine ⟨t,ht,?_⟩
  intro hmem
  have hx : x+t • v ∈ f.symm '' K := ⟨f (x+t • v),hmem,f.left_inv (by rw [hs]; trivial)⟩
  have hb := hbound _ hx
  have hh : ‖t • v‖ ≤ ‖x+t • v‖+‖x‖ := by
    calc
      _ = ‖(x+t • v)-x‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht] at hh
  have he : t*‖v‖=C+‖x‖+1 := div_mul_cancel₀ _ hvp.ne'
  rw [he] at hh
  linarith

lemma radial_upper_enclosure (f : OpenPartialHomeomorph Point Point)
    (hs : f.source=univ) {p : Point} {h U : ℝ} (hU : 0≤U)
    (hball : closedBall p h ⊆ f.target)
    (hb : ∀ x ∈ sphere p h, dist (f.symm x) (f.symm p) ≤ U) :
    ∀ x ∈ closedBall p h, dist (f.symm x) (f.symm p) ≤ U := by
  intro x hx
  by_cases he : f.symm x=f.symm p
  · simpa only [he,dist_self] using hU
  let v := f.symm x-f.symm p
  have hv : v≠0 := sub_ne_zero.mpr he
  obtain ⟨t,ht,hexit⟩ := ray_image_leaves_compact f hs (closedBall p h)
    (isCompact_closedBall _ _) hball (f.symm x) v hv
  have hf : Continuous f := continuousOn_univ.mp (by simpa only [hs] using f.continuousOn)
  have hcont : Continuous (fun s : ℝ => dist (f (f.symm x+s • v)) p) :=
    (hf.comp
      (continuous_const.add (continuous_id.smul continuous_const))).dist continuous_const
  have h0 : dist (f (f.symm x+(0:ℝ) • v)) p ≤ h := by
    simpa only [zero_smul,add_zero,f.right_inv (hball hx)] using (Metric.mem_closedBall.mp hx)
  have h1 : h ≤ dist (f (f.symm x+t • v)) p := (not_le.mp hexit).le
  obtain ⟨s,hs',heq⟩ := intermediate_value_Icc ht hcont.continuousOn ⟨h0,h1⟩
  have hh := hb (f (f.symm x+s • v)) heq
  rw [f.left_inv (by rw [hs]; trivial)] at hh
  have hn : dist (f.symm x+s • v) (f.symm p)=(1+s)*dist (f.symm x) (f.symm p) := by
    rw [dist_eq_norm,show f.symm x+s • v-f.symm p=(1+s) • v by dsimp [v]; module]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by linarith [hs'.1])]
    rfl
  rw [hn] at hh
  nlinarith [dist_nonneg (x:=f.symm x) (y:=f.symm p),hs'.1]

lemma radial_lower_exterior (f : OpenPartialHomeomorph Point Point)
    (hs : f.source=univ) {p : Point} (hp : p∈f.target) {h V : ℝ} (hh : 0≤h)
    (hb : ∀ x ∈ sphere p h, V ≤ dist (f.symm x) (f.symm p)) :
    ∀ x ∈ f.target, h ≤ dist x p → V ≤ dist (f.symm x) (f.symm p) := by
  intro x hx hxp
  let v := f.symm x-f.symm p
  have hf : Continuous f := continuousOn_univ.mp (by simpa only [hs] using f.continuousOn)
  have hcont : Continuous (fun s : ℝ => dist (f (f.symm p+s • v)) p) :=
    (hf.comp
      (continuous_const.add (continuous_id.smul continuous_const))).dist continuous_const
  have h0 : dist (f (f.symm p+(0:ℝ) • v)) p ≤ h := by simpa [f.right_inv hp] using hh
  have h1 : h ≤ dist (f (f.symm p+(1:ℝ) • v)) p := by simpa [v,f.right_inv hx] using hxp
  obtain ⟨s,hs',heq⟩ := intermediate_value_Icc (show (0:ℝ)≤1 by norm_num) hcont.continuousOn ⟨h0,h1⟩
  have hb' := hb (f (f.symm p+s • v)) heq
  rw [f.left_inv (by rw [hs]; trivial),dist_eq_norm,add_sub_cancel_left,
    norm_smul,Real.norm_eq_abs,abs_of_nonneg hs'.1] at hb'
  change V ≤ dist (f.symm x) (f.symm p)
  rw [dist_eq_norm]
  exact hb'.trans (mul_le_of_le_one_left (norm_nonneg v) hs'.2)

lemma radial_inner_enclosure (f : OpenPartialHomeomorph Point Point)
    (hs : f.source=univ) {p : Point} (hp : p∈f.target) {h V : ℝ} (hh : 0≤h)
    (hb : ∀ x ∈ sphere p h, V ≤ dist (f.symm x) (f.symm p)) :
    ball (f.symm p) V ⊆ f.symm '' ball p h := by
  intro y hy
  have hyt : f y∈f.target := f.map_source (by rw [hs]; trivial)
  have he : f.symm (f y)=y := f.left_inv (by rw [hs]; trivial)
  refine ⟨f y,?_,he⟩
  by_contra hn
  have hd := radial_lower_exterior f hs hp hh hb (f y) hyt (not_lt.mp hn)
  rw [he] at hd
  exact (not_lt_of_ge hd) hy

end PlanarHalving.Spatial

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows RankCoordinates Zoom
open scoped Topology unitInterval

lemma allowed_disjoint_in_gap (μ : Measure I) [NullSingletonClass μ]
    (K : Window) (Q : Point ≃L[ℝ] Point) (g : Subwindows K → Point →L[ℝ] ℝ)
    (hind : ∀ J : Subwindows K, μ (carrier J.val) ≠ 0 →
      ∃ i j : Subwindows K, carrier i.val ⊆ carrier J.val ∧
        carrier j.val ⊆ carrier J.val ∧
        Function.Injective (fun v : Point => (g i v,g j v)))
    {s t : I} (hs : s∈Ioo (lower K) (upper K)) (ht : t∈Ioo (lower K) (upper K))
    (hgap : μ (Ioo s t) ≠ 0) :
    Disjoint (Directions.allowed Q g (fun i => (lower i.val:ℝ)) (fun i => (upper i.val:ℝ)) s)
      (Directions.allowed Q g (fun i => (lower i.val:ℝ)) (fun i => (upper i.val:ℝ)) t) := by
  obtain ⟨J,hsJ,hJt,hJ⟩ := exists_positive_inside μ hgap
  have hJK := carrier_subset_of_inside (hs.1.trans hsJ) (hJt.trans ht.2)
  obtain ⟨i,j,hi,hj,hij⟩ := hind ⟨J,hJK⟩ hJ
  exact Directions.allowed_disjoint Q g _ _ i j
    (hsJ.trans_le (endpoints_of_subset hi).1) ((endpoints_of_subset hi).2.trans_lt hJt)
    (hsJ.trans_le (endpoints_of_subset hj).1) ((endpoints_of_subset hj).2.trans_lt hJt) hij

lemma pointwise_radial (F : ℕ → Configuration) (hR : Tendsto (fun n => (F n).R) atTop atTop)
    {K A B : Window} (hAB : Before A B) (hKA : Before K A) (hKB : Before K B)
    (hA : ∀ n, 0 < length (F n).R A) (hB : ∀ n, 0 < length (F n).R B)
    (G : Subwindows K → Point → I)
    (hjoint : ∀ i p, ContinuousAt (G i) p → Tendsto
      (fun q : ℕ × Point => (F q.1).extendedRank true A B i.val q.2)
      (atTop ×ˢ 𝓝 p) (𝓝 (G i p)))
    (hGaed : ∀ i, ∀ᵐ p ∂(volume : Measure Point), DifferentiableAt ℝ (fun x => (G i x : ℝ)) p)
    {p : Point} (hp : p∈Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0)
    (hd : ∀ i, DifferentiableAt ℝ (fun x => (G i x : ℝ)) p)
    (μ : Measure I) [NullSingletonClass μ] (hpos : μ (carrier K)≠0)
    (hind : ∀ J : Subwindows K, μ (carrier J.val) ≠ 0 →
      ∃ i j : Subwindows K, carrier i.val ⊆ carrier J.val ∧
        carrier j.val ⊆ carrier J.val ∧
        Function.Injective (fun v : Point =>
          ((fderiv ℝ (fun x => (G i x : ℝ)) p) v,(fderiv ℝ (fun x => (G j x : ℝ)) p) v)))
    (t : Fin 3 → I) (ht : ∀ i, t i∈Ioo (lower K) (upper K))
    (htgap : ∀ i j, i<j → μ (Ioo (t i) (t j))≠0)
    (L : ℕ → Point ≃L[ℝ] Point) (v : Fin 3 → Point)
    (hv : ∀ i j, i≠j → detPair (v i) (v j)≠0)
    (hL : ∀ n i, detPair (L n (1,(F n).timeSlope (t i))) (v i)=0) :
    ∃ C₀ : ℝ, 0<C₀ ∧ ∀ T : ℝ, 1≤T → ∀ᶠ h in 𝓝[>] (0:ℝ), ∀ᶠ n in atTop,
      RadialCompare (fun x => L n (((F n).rankChart hAB (hA n) (hB n)).symm x)) p h C₀ T := by
  let : Nonempty (Subwindows K) := ⟨⟨K,Subset.rfl⟩⟩
  let D := fun i : Subwindows K => fderiv ℝ (fun x => (G i x : ℝ)) p
  have hC (i : Subwindows K) : Before i.val A ∧ Before i.val B :=
    ⟨(endpoints_of_subset i.property).2.trans hKA,(endpoints_of_subset i.property).2.trans hKB⟩
  have hne (t : I) (ht : t∈Ioo (lower K) (upper K)) :=
    actual_allowed_nonempty F hR hAB (fun i : Subwindows K => i.val) hC G hjoint hGaed hp hd
      t (ht.2.le.trans hKA) (ht.2.le.trans hKB)
  obtain ⟨τ₁,τ₂,τ₃,z₁,z₂,z₃,hτ₁,hτ₂,hτ₃,h12,h23,hz₁,hz₂,hz₃,hd12,hd23,hd13⟩ :=
    three_directions_of_independent μ K hpos reflectFirst D hne hind
  obtain ⟨B',d,_,hB'⟩ := singleton_target_frame z₁ z₂ z₃ hd12 hd23 hd13
  let S := fun j => Directions.allowed reflectFirst D (fun i => (lower i.val:ℝ))
    (fun i => (upper i.val:ℝ)) (t j)
  have hdis (i j : Fin 3) (hij : i≠j) : Disjoint (S i) (S j) := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact allowed_disjoint_in_gap μ K reflectFirst D hind (ht i) (ht j) (htgap i j h)
    · exact (allowed_disjoint_in_gap μ K reflectFirst D hind (ht j) (ht i) (htgap j i h)).symm
  obtain ⟨ε,hε,hcond⟩ := exists_frameCondition B' S
    (fun j => Directions.allowed_closed _ _ _ _ _) (fun _ _ hx => hx.1) hdis v hv
  let C₀ : ℝ := (‖B'.toContinuousLinearMap‖+1)/(ε/‖B'.symm.toContinuousLinearMap‖)
  have hl : 0<ε/‖B'.symm.toContinuousLinearMap‖ := div_pos hε (equiv_opNorm_pos _)
  have hC₀ : 0<C₀ := div_pos (by positivity) hl
  refine ⟨C₀,hC₀,?_⟩
  apply actual_radial_comparison F hR hAB hA hB (fun i : Subwindows K => i.val) hC
    (fun i => eventually_length_pos _ hR i.val) D (fun i => (G i p:ℝ)) p hp
    (fun i R hR ε hε => rank_firstOrder_filter F A B i.val (G i) (hjoint i) (hGaed i) (hd i) hR hε)
    τ₁ τ₂ τ₃ h12 h23
    (fun i => ?_) (fun i => ?_) (foliationTriple z₁ z₂ z₃) (fun i => ?_) B' d hB' L t
    (fun i => (ht i).2.le.trans hKA) (fun i => (ht i).2.le.trans hKB) v ε hε hcond hL C₀
  · dsimp [C₀]; rw [div_mul_cancel₀ _ hl.ne']; linarith
  · cases i <;> first | exact hτ₁.2.le.trans hKA | exact hτ₂.2.le.trans hKA | exact hτ₃.2.le.trans hKA
  · cases i <;> first | exact hτ₁.2.le.trans hKB | exact hτ₂.2.le.trans hKB | exact hτ₃.2.le.trans hKB
  · cases i <;> first | exact hz₁ | exact hz₂ | exact hz₃

end PlanarHalving.RankLimits

namespace PlanarHalving.TimeWindows
open Set Filter MeasureTheory
open scoped Topology unitInterval

lemma exists_two_positive_inside (μ : Measure I) [NullSingletonClass μ]
    (K : Window) (hpos : μ (carrier K)≠0) :
    ∃ J H : Window, lower K<lower J ∧ upper J<lower H ∧ upper H<upper K ∧
      μ (carrier J)≠0 ∧ μ (carrier H)≠0 := by
  have hpos' : μ (Ioo (lower K) (upper K))≠0 := by rwa [measure_interior_eq μ K]
  have hsupp : ∀ᵐ x ∂μ, x∈μ.support := μ.support_mem_ae
  obtain ⟨x,hx,hxs⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos'
    (hsupp.filter_mono ae_restrict_le)
  obtain ⟨y,hy,hys,hyx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos'
    ((hsupp.and (μ.ae_ne x)).filter_mono ae_restrict_le)
  have hpair : ∃ a b : I, a∈Ioo (lower K) (upper K) ∧ b∈Ioo (lower K) (upper K) ∧
      a∈μ.support ∧ b∈μ.support ∧ a<b := by
    rcases lt_or_gt_of_ne hyx with h | h
    · exact ⟨y,x,hy,hx,hys,hxs,h⟩
    · exact ⟨x,y,hx,hy,hxs,hys,h⟩
  obtain ⟨a,b,ha,hb,has,hbs,hab⟩ := hpair
  obtain ⟨c,hac,hcb⟩ := exists_between hab
  have hleft : μ (Ioo (lower K) c)≠0 := ne_of_gt
    ((Measure.mem_support_iff_forall a).mp has _ (Ioo_mem_nhds ha.1 hac))
  have hright : μ (Ioo c (upper K))≠0 := ne_of_gt
    ((Measure.mem_support_iff_forall b).mp hbs _ (Ioo_mem_nhds hcb hb.2))
  obtain ⟨J,hJ1,hJ2,hJ⟩ := exists_positive_inside μ hleft
  obtain ⟨H,hH1,hH2,hH⟩ := exists_positive_inside μ hright
  exact ⟨J,H,hJ1,hJ2.trans hH1,hH2,hJ,hH⟩

def CommonChoice (K : Window) := {q : Window × Window × Window //
  lower K<lower q.1 ∧ upper q.1<lower q.2.1 ∧ upper q.2.1<upper K ∧
  lower q.1<lower q.2.2 ∧ upper q.2.2<upper q.1}
instance (K : Window) : Countable (CommonChoice K) := by unfold CommonChoice; infer_instance

noncomputable def CommonChoice.time {K : Window} (q : CommonChoice K) : Fin 3 → I :=
  ![lower q.val.1,upper q.val.1,upper q.val.2.1]

lemma CommonChoice.time_mem {K : Window} (q : CommonChoice K) (i : Fin 3) :
    q.time i∈Ioo (lower K) (upper K) := by
  have h := q.property
  fin_cases i <;> dsimp [CommonChoice.time]
  · exact ⟨h.1,(lower_lt_upper q.val.1).trans (h.2.1.trans ((lower_lt_upper q.val.2.1).trans h.2.2.1))⟩
  · exact ⟨h.1.trans (lower_lt_upper q.val.1),h.2.1.trans ((lower_lt_upper q.val.2.1).trans h.2.2.1)⟩
  · exact ⟨h.1.trans ((lower_lt_upper q.val.1).trans (h.2.1.trans (lower_lt_upper q.val.2.1))),h.2.2.1⟩

lemma CommonChoice.time_strictMono {K : Window} (q : CommonChoice K) : StrictMono q.time := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  fin_cases i <;> dsimp [CommonChoice.time]
  · exact lower_lt_upper q.val.1
  · exact q.property.2.1.trans (lower_lt_upper q.val.2.1)

lemma CommonChoice.positive_gaps {K : Window} (q : CommonChoice K)
    (μ : Measure I) [NullSingletonClass μ]
    (hJ : μ (carrier q.val.1)≠0) (hH : μ (carrier q.val.2.1)≠0) :
    ∀ i j, i<j → μ (Ioo (q.time i) (q.time j))≠0 := by
  have hj : μ (Ioo (lower q.val.1) (upper q.val.1))≠0 := by rwa [measure_interior_eq]
  have hh : μ (Ioo (lower q.val.2.1) (upper q.val.2.1))≠0 := by rwa [measure_interior_eq]
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals try (norm_num at hij)
  all_goals dsimp [CommonChoice.time]
  · exact hj
  · apply ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hj) (measure_mono ?_))
    exact Ioo_subset_Ioo_right ((q.property.2.1.trans (lower_lt_upper q.val.2.1)).le)
  · apply ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hh) (measure_mono ?_))
    exact Ioo_subset_Ioo_left q.property.2.1.le

lemma exists_commonChoice (μ : Measure I) [NullSingletonClass μ]
    (K : Window) (hpos : μ (carrier K)≠0) :
    ∃ q : CommonChoice K, μ (carrier q.val.1)≠0 ∧
      μ (carrier q.val.2.1)≠0 ∧ μ (carrier q.val.2.2)≠0 := by
  obtain ⟨J,H,hJ1,hJH,hH2,hJ,hH⟩ := exists_two_positive_inside μ K hpos
  have hJi : μ (Ioo (lower J) (upper J))≠0 := by rwa [measure_interior_eq]
  obtain ⟨K₀,hK1,hK2,hK⟩ := exists_positive_inside μ hJi
  exact ⟨⟨(J,H,K₀),hJ1,hJH,hH2,hK1,hK2⟩,hJ,hH,hK⟩

end PlanarHalving.TimeWindows

namespace PlanarHalving.Limits
open Set MeasureTheory

lemma positive_countable_selection {X ι : Type*} [MeasurableSpace X] [Countable ι]
    (μ : Measure X) (T : Set X) (hTm : MeasurableSet T) (hT : μ T≠0) (E : ι → Set X)
    (hcover : ∀ᵐ x ∂μ.restrict T, ∃ i, x∈E i) :
    ∃ i, μ (T∩E i)≠0 := by
  by_contra hn
  have hn' : ∀ i, μ (T∩E i)=0 := by simpa only [not_exists,not_not] using hn
  have hzero : μ (⋃ i, T∩E i)=0 := measure_iUnion_null hn'
  have hnull : ∀ᵐ x ∂μ.restrict T, x∉⋃ i, E i := by
    apply (ae_restrict_iff' hTm).mpr
    rw [ae_iff]
    convert hzero using 1
    congr 1
    ext x
    simp only [mem_ofPred_eq,Classical.not_imp,not_not,mem_iUnion,mem_inter_iff]
    aesop
  have he : ∀ᵐ x ∂μ.restrict T, False := by
    filter_upwards [hcover,hnull] with x hx hn
    exact hn (mem_iUnion.mpr hx)
  have hh : μ.restrict T univ=0 := by simpa only [ae_iff,not_false_eq_true,ofPred_true] using he
  exact hT (by simpa only [Measure.restrict_apply_univ] using hh)

end PlanarHalving.Limits

end OAI
