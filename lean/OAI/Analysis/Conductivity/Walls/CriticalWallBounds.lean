import Mathlib
import OAI.Analysis.Conductivity.Walls.WallMomentAmplitudeBounds
import OAI.Analysis.Conductivity.Variational.CompactParametricBounds

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

lemma wallMatrix_norm_le {A B : Box3 → ℝ} {x : Coord3} {M : ℝ}
    (hM : 0≤M) (hA : |A (boxCoordinates x)|≤M) (hB : |B (boxCoordinates x)|≤M) :
    ‖wallMatrix A B x‖≤M := by
  apply Matrix.norm_le_iff hM |>.mpr
  intro i j
  fin_cases i <;> fin_cases j
  all_goals first | exact hA | exact hB | (change |(0:ℝ)|≤M; simpa only [abs_zero] using hM)

lemma wallHomogeneousNumerator_derivative {v : Box3 → ℝ} {a : (ℝ×ℝ) → ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) (ha : ContDiff ℝ (↑(⊤ : ℕ∞)) a) (p : Box3) :
    wallDerivative (wallHomogeneousNumerator (1,0) v a) p=
      -2*a p.1*wallAlong (1,0) (wallDerivative v) p-
       wallAlong (1,0) (fun q : Box3 => a q.1) p*wallDerivative v p := by
  have hA : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun q : Box3 => a q.1) := ha.comp contDiff_fst
  have hG := wallHomogeneousNumerator_smooth (1,0) hv ha
  have hh := (wall_homogeneous_flux_equations (1,0) hv ha p).2
  rw [wallAlong_mul (1,0) (hA.differentiable (by simp))
      ((wallDerivative_smooth hv).differentiable (by simp)),
    wallDerivative_add ((hA.mul (wallAlong_smooth (1,0) hv)).differentiable (by simp))
      (hG.differentiable (by simp)),
    wallDerivative_mul (hA.differentiable (by simp))
      ((wallAlong_smooth (1,0) hv).differentiable (by simp)),
    wallDerivative_pullback (ha.differentiable (by simp)),wall_mixed_commute (1,0) hv] at hh
  linarith

lemma wallAlong_pullback_box {a : (ℝ×ℝ) → ℝ} (ha : Differentiable ℝ a) (d : ℝ×ℝ) (p : Box3) :
    wallAlong d (fun q : Box3 => a q.1) p=fderiv ℝ a p.1 d := by
  change fderiv ℝ (a∘Prod.fst) p (d,0)=_
  rw [fderiv_comp p (ha p.1) differentiableAt_fst,fderiv_fst]
  rfl

theorem wallHomogeneousTensor_C0 {χ v : Box3 → ℝ} {a : (ℝ×ℝ) → ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) (ha : ContDiff ℝ (↑(⊤ : ℕ∞)) a)
    {ε M κ : ℝ} (hε : 0≤ε) (hM : 0≤M) (hκ : 0<κ)
    (hχ : ∀ p,|χ p|≤1)
    (ha₀ : ∀ q,|a q|≤ε) (ha₁ : ∀ q,|fderiv ℝ a q (1,0)|≤ε)
    (hvz : ∀ p∈tsupport χ,∀ t∈Icc (0:ℝ) 1,|wallDerivative v (p.1,t*p.2)|≤M)
    (hvsz : ∀ p∈tsupport χ,∀ t∈Icc (0:ℝ) 1,|wallAlong (1,0) (wallDerivative v) (p.1,t*p.2)|≤M)
    (hden : ∀ p∈tsupport χ,κ≤|wallQuotient (wallDerivative v) p|) (x : Coord3) :
    ‖wallHomogeneousTensor χ v a x‖≤(1+3*M/κ)*ε := by
  let p := boxCoordinates x
  have hK : 0≤(1+3*M/κ)*ε := by positivity
  by_cases hp : p∈tsupport χ
  · have hnum : |wallQuotient (wallHomogeneousNumerator (1,0) v a) p|≤3*ε*M := by
      apply wallQuotient_abs_bound
      intro t ht
      rw [wallHomogeneousNumerator_derivative hv ha,wallAlong_pullback_box (ha.differentiable (by simp))]
      calc
        _ ≤ |-2*a p.1*wallAlong (1,0) (wallDerivative v) (p.1,t*p.2)|+
          |fderiv ℝ a p.1 (1,0)*wallDerivative v (p.1,t*p.2)| := abs_sub _ _
        _ ≤ 2*ε*M+ε*M := by
          simp only [abs_mul,abs_neg,show |(2:ℝ)|=2 by norm_num]
          gcongr
          · exact ha₀ p.1
          · exact hvsz p hp t ht
          · exact ha₁ p.1
          · exact hvz p hp t ht
        _ = _ := by ring
    have hB : |wallQuotient (wallHomogeneousNumerator (1,0) v a) p/
        wallQuotient (wallDerivative v) p|≤3*ε*M/κ := by
      rw [abs_div]
      exact div_le_div₀ (by positivity) hnum hκ (hden p hp)
    apply wallMatrix_norm_le hK
    · change |χ p*a p.1|≤_
      rw [abs_mul]
      calc
        _ ≤ 1*ε := mul_le_mul (hχ p) (ha₀ p.1) (abs_nonneg _) (by norm_num)
        _ ≤ _ := by
          have ht : 0≤3*M/κ := by positivity
          nlinarith
    · change |χ p*(_ / _)|≤_
      rw [abs_mul]
      calc
        _ ≤ 1*(3*ε*M/κ) := mul_le_mul (hχ p) hB (abs_nonneg _) (by norm_num)
        _ ≤ _ := by nlinarith [show 3*ε*M/κ=(3*M/κ)*ε by ring]
  · have hz : χ p=0 := image_eq_zero_of_notMem_tsupport hp
    apply wallMatrix_norm_le hK <;> change |χ p*_|≤_ <;> rw [hz,zero_mul,abs_zero] <;> exact hK

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set Filter Topology

variable {P : Type*} [TopologicalSpace P]

def wallNormalHull (K : Set Box3) : Set Box3 :=
  (fun pt : Box3×ℝ => (pt.1.1,pt.2*pt.1.2)) '' (K ×ˢ Icc (0:ℝ) 1)

lemma wallNormalHull_compact {K : Set Box3} (hK : IsCompact K) : IsCompact (wallNormalHull K) :=
  (hK.prod isCompact_Icc).image (continuous_fst.fst.prodMk (continuous_snd.mul continuous_fst.snd))

lemma mem_wallNormalHull {K : Set Box3} {x : Box3} (hx : x∈K) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    (x.1,t*x.2)∈wallNormalHull K := ⟨(x,t),⟨hx,ht⟩,rfl⟩

theorem wall_field_uniform_bounds {v : P → Box3 → ℝ} {p₀ : P} {K : Set Box3}
    (hK : IsCompact K)
    (hvz : Continuous (fun px : P×Box3 => wallDerivative (v px.1) px.2))
    (hvsz : Continuous (fun px : P×Box3 => wallAlong (1,0) (wallDerivative (v px.1)) px.2))
    (hD : Continuous (fun px : P×Box3 => wallQuotient (wallDerivative (v px.1)) px.2))
    (hne : ∀ x∈K,wallQuotient (wallDerivative (v p₀)) x≠0) :
    ∃ M κ : ℝ,0<M ∧ 0<κ ∧ ∀ᶠ p in 𝓝 p₀,
      (∀ x∈K,∀ t∈Icc (0:ℝ) 1,|wallDerivative (v p) (x.1,t*x.2)|≤M) ∧
      (∀ x∈K,∀ t∈Icc (0:ℝ) 1,|wallAlong (1,0) (wallDerivative (v p)) (x.1,t*x.2)|≤M) ∧
      (∀ x∈K,κ≤|wallQuotient (wallDerivative (v p)) x|) := by
  obtain ⟨M₁,hM₁,hb₁⟩ := compact_parametric_abs_bound (f:=fun p x => wallDerivative (v p) x) (p₀:=p₀) (wallNormalHull_compact hK) hvz
  obtain ⟨M₂,hM₂,hb₂⟩ := compact_parametric_abs_bound (f:=fun p x => wallAlong (1,0) (wallDerivative (v p)) x) (p₀:=p₀) (wallNormalHull_compact hK) hvsz
  obtain ⟨κ,hκ,hlo⟩ := compact_parametric_abs_lower (f:=fun p x => wallQuotient (wallDerivative (v p)) x) hK hD hne
  refine ⟨M₁+M₂,κ,add_pos hM₁ hM₂,hκ,?_⟩
  filter_upwards [hb₁,hb₂,hlo] with p hp₁ hp₂ hp₃
  refine ⟨?_,?_,hp₃⟩
  · intro x hx t ht
    exact (hp₁ _ (mem_wallNormalHull hx ht)).trans (le_add_of_nonneg_right hM₂.le)
  · intro x hx t ht
    exact (hp₂ _ (mem_wallNormalHull hx ht)).trans (le_add_of_nonneg_left hM₁.le)

end ScalarConductivity



namespace ScalarConductivity
open Set MeasureTheory Matrix Filter Topology
open scoped Matrix.Norms.Elementwise
variable {P : Type*} [TopologicalSpace P] [FirstCountableTopology P] [LocallyCompactSpace P]

theorem compact_wall_transfer_exists {l r a b σ lam : ℝ}
    (hlr : l<r) (hab : a<b) (hσ : σ≠0) (hlam : lam≠0)
    {v : P → Box3 → ℝ} {p₀ : P}
    (hvsmooth : ∀ p,ContDiff ℝ (↑(⊤ : ℕ∞)) (v p))
    (hv : Continuous (fun px : P×Box3 => v px.1 px.2))
    (hvs : Continuous (fun px : P×Box3 => wallAlong (1,0) (v px.1) px.2))
    (hvz : Continuous (fun px : P×Box3 => wallDerivative (v px.1) px.2))
    (hvsz : Continuous (fun px : P×Box3 => wallAlong (1,0) (wallDerivative (v px.1)) px.2))
    (hD : Continuous (fun px : P×Box3 => wallQuotient (wallDerivative (v px.1)) px.2))
    (hz : ∀ p q,wallDerivative (v p) (q,0)=0)
    (hlim : ∀ q : ℝ×ℝ,v p₀ (q,0)=σ*Real.exp (-lam*q.1))
    {Ω : Set Box3} (hΩ : IsOpen Ω) (hbΩ : Bornology.IsBounded Ω)
    (hcore : (Icc l r ×ˢ Icc a b) ×ˢ {(0:ℝ)}⊆Ω)
    (hne₀ : ∀ x∈Ω,wallQuotient (wallDerivative (v p₀)) x≠0) :
    ∃ χ : Box3 → ℝ,ContDiff ℝ (↑(⊤ : ℕ∞)) χ ∧ HasCompactSupport χ ∧
      tsupport χ⊆Ω ∧ (∀ x,χ x∈Icc 0 1) ∧
      (∀ q∈Icc l r ×ˢ Icc a b,χ =ᶠ[𝓝 (q,0)] (fun _ => 1)) ∧
      ∃ L : ℝ,0<L ∧ ∀ᶠ p in 𝓝 p₀,∀ m : Fin 3 → ℝ,
        ∃ f : (ℝ×ℝ) → ℝ,ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧ HasCompactSupport f ∧
          tsupport f⊆Icc l r ×ˢ Ioo a b ∧
          let H := wallHomogeneousTensor χ (v p) f
          ContDiff ℝ (↑(⊤ : ℕ∞)) H ∧ HasCompactSupport H ∧
          tsupport H⊆boxCoordinates ⁻¹' Ω ∧ (∀ x,(H x).IsSymm) ∧
          (∀ x,‖H x‖≤L*‖m‖) ∧
          (let u := wallCoordinatePair (v p)
           let r := fun (j : Fin 2) (x : Box3) => symmetricSource H u j (boxCoordinates.symm x)
           let U := (Set.univ : Set (ℝ×ℝ)) ×ˢ Ioi (0:ℝ)
           (∫ x in U,r 0 x)=m 0 ∧ (∫ x in U,r 1 x)=m 1 ∧
           (∫ x in U,v p x*r 0 x-x.1.1*r 1 x)=m 2) := by
  have hK : IsCompact ((Icc l r ×ˢ Icc a b) ×ˢ {(0:ℝ)}) :=
    (isCompact_Icc.prod isCompact_Icc).prod (isCompact_singleton : IsCompact ({(0:ℝ)}))
  obtain ⟨χ,hχ,hsχ,hχΩ,hχb,hχcore⟩ := exists_smooth_core_cutoff hK hΩ hbΩ hcore
  obtain ⟨B,hB,hinv⟩ := actual_wall_amplitude_inverse hlr hab hσ hlam (hvsmooth p₀) hv hvs hlim
  obtain ⟨M,κ,hM,hκ,hfield⟩ := wall_field_uniform_bounds hsχ hvz hvsz hD
    (fun x hx => hne₀ x (hχΩ hx))
  have hL : 0<(1+3*M/κ)*B := by positivity
  refine ⟨χ,hχ,hsχ,hχΩ,hχb,fun q hq => hχcore (q,0) ⟨hq,rfl⟩,
    (1+3*M/κ)*B,hL,?_⟩
  filter_upwards [hinv,hfield] with p hp hf
  intro m
  obtain ⟨f,hfsm,hfcomp,hfsupp,hfm,hfb⟩ := hp (-m)
  have hne : ∀ x∈tsupport χ,wallQuotient (wallDerivative (v p)) x≠0 := by
    intro x hx hn
    have h := hf.2.2 x hx
    rw [hn,abs_zero] at h
    exact (not_le_of_gt hκ) h
  have hcut : ∀ q,χ (q,0)*f q=f q := by
    intro q
    by_cases hn : f q=0
    · simp only [hn,mul_zero]
    · have hq := hfsupp (subset_tsupport f hn)
      have he := (hχcore (q,0) ⟨⟨hq.1,Ioo_subset_Icc_self hq.2⟩,rfl⟩).eq_of_nhds
      rw [he,one_mul]
  refine ⟨f,hfsm,hfcomp,hfsupp,wallHomogeneousTensor_smooth hχ (hvsmooth p) hfsm hne,
    (wallHomogeneousTensor_compact hsχ).1,
    (wallHomogeneousTensor_compact hsχ).2.trans (preimage_mono hχΩ),
    wallMatrix_symmetric _ _,?_,?_⟩
  · intro x
    have heq : ‖-m‖=‖m‖ := norm_neg m
    have hval (q) : |f q|≤B*‖m‖ := by simpa only [heq] using (hfb q).1
    have hder (q) : |fderiv ℝ f q (1,0)|≤B*‖m‖ := by simpa only [heq] using (hfb q).2
    have hsmall := wallHomogeneousTensor_C0 (hvsmooth p) hfsm
      (mul_nonneg hB.le (norm_nonneg m)) hM.le hκ
      (fun q => by rw [abs_of_nonneg (hχb q).1]; exact (hχb q).2)
      hval hder hf.1 hf.2.1 hf.2.2 x
    simpa only [mul_assoc] using hsmall
  · have ht := wallHomogeneousTensor_transfers hχ hsχ (hvsmooth p) hfsm (hz p) hne hcut
    have h₀ := hfm 0
    have h₁ := hfm 1
    have h₂ := hfm 2
    change (∫ q,f q*1)= -m 0 at h₀
    change (∫ q,f q*wallAlong (1,0) (v p) (q,0))= -m 1 at h₁
    change (∫ q,f q*(v p (q,0)-q.1*wallAlong (1,0) (v p) (q,0)))= -m 2 at h₂
    simp only [mul_one] at h₀
    simpa only [h₀,h₁,h₂,neg_neg] using ht

end ScalarConductivity

end

end OAI
