import OAI.Analysis.CircleDomains.Sobolev.PrincipalSmoothLimit

namespace OAI

/-! A bounded multiplier tending almost everywhere to zero annihilates
both the fixed and variable parts of the principal derivative on any
finite-measure set. This is used for the reflection defect. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma PrincipalMapLimit.exists_localized_derivative_error
    {g : PlaneL2} {k R : ℝ} {S : PrincipalSmoothApproximation g k R} (L : PrincipalMapLimit S)
    {A : Set ℂ} (hA : MeasurableSet A) (hfin : volume A ≠ ∞)
    (δ : ℕ → ℂ → ℂ) (hδ : ∀n,AEStronglyMeasurable (δ n) volume)
    {B : ℝ} (hB : 0≤B) (hb : ∀n,∀ᵐz ∂volume,‖δ n z‖≤B)
    (ht : ∀ᵐz ∂volume,Tendsto (fun n => δ n z) atTop (𝓝 0)) :
    ∃q : ℕ → PlaneL2,Tendsto q atTop (𝓝 0) ∧ ∀n,∀ᵐz ∂volume,
      q n z=A.indicator (fun w => δ n w*partialZ (S.map (L.index n)) w) z := by
  let χ : ℂ → ℂ := A.indicator (fun _ => 1)
  have hχ : AEStronglyMeasurable χ volume := aestronglyMeasurable_const.indicator hA
  have hbχ : ∀ᵐz ∂volume,‖χ z‖≤(1:ℝ) := by
    filter_upwards [] with z
    by_cases hz : z∈A <;> simp [χ,hz]
  let M := multiplier χ hχ zero_le_one hbχ
  let b := indicatorConstLp 2 hA hfin (1:ℂ)
  let f (n : ℕ) := b+M (beurling ((S.density (L.index n)).toLp 2 (μ:=volume)))
  have hf : Tendsto f atTop (𝓝 (b+M (beurling g))) :=
    tendsto_const_nhds.add (M.continuous.tendsto _ |>.comp
      (beurling.continuous.tendsto _ |>.comp (S.strong_density.comp L.index_strict.tendsto_atTop)))
  let q (n : ℕ) := multiplier (δ n) (hδ n) hB (hb n) (f n)
  have hq : Tendsto q atTop (𝓝 0) := by
    have hh := multiplier_variable_convergence δ (fun _ => 0) hδ aestronglyMeasurable_zero hB hb
      (.of_forall fun _ => by simpa using hB) ht f (b+M (beurling g)) hf
    have hz : multiplier (fun _ : ℂ => (0:ℂ)) aestronglyMeasurable_zero hB
        (.of_forall fun _ => by simpa using hB) (b+M (beurling g))=0 := by
      apply Lp.ext
      filter_upwards [multiplier_ae (fun _ : ℂ => (0:ℂ)) aestronglyMeasurable_zero hB
        (.of_forall fun _ => by simpa using hB) (b+M (beurling g)),Lp.coeFn_zero ℂ 2 volume] with z hz h0
      rw [hz,h0,Pi.zero_apply,zero_mul]
    simpa only [hz] using hh
  refine ⟨q,hq,?_⟩
  intro n
  filter_upwards [multiplier_ae (δ n) (hδ n) hB (hb n) (f n),Lp.coeFn_add b (M (beurling
      ((S.density (L.index n)).toLp 2 (μ:=volume)))),
    indicatorConstLp_coeFn (p:=2) (hs:=hA) (hμs:=hfin) (c:=(1:ℂ)),
    multiplier_ae χ hχ zero_le_one hbχ (beurling ((S.density (L.index n)).toLp 2 (μ:=volume))),
    (schwartz_smoothL2 (S.density (L.index n))).beurling.representative_ae] with z hqz hfz hcz hMz hBz
  simp only [Pi.add_apply] at hfz
  change q n z=_
  rw [hqz,hfz,hcz,hMz]
  change δ n z*(A.indicator (fun _ => (1:ℂ)) z+χ z*_) = _
  by_cases hz : z∈A
  · simp only [χ,indicator_of_mem hz,one_mul]
    rw [hBz]
    exact congrArg (fun v : ℂ => δ n z*v) (S.partials (L.index n) z).2.symm
  · simp [χ,hz]

end CircleDomainRigidity

end

end OAI
