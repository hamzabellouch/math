import OAI.Analysis.Mahler.RawAlternationDerivative

namespace OAI

open ContinuousAlternatingMap Filter
open scoped Topology
namespace Mahler
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The derivative slot is numbered zero; all old slots follow in order. -/
def rawFrontFin (n : ℕ) : Fin 1 ⊕ Fin n ≃ Fin (n+1) :=
  finSumFinEquiv.trans (finCongr (Nat.add_comm 1 n))

@[simp] lemma rawFrontFin_inl (n : ℕ) (i : Fin 1) : rawFrontFin n (Sum.inl i) = 0 := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl

@[simp] lemma rawFrontFin_inr {n : ℕ} (i : Fin n) :
    rawFrontFin n (Sum.inr i) = i.succ := by
  apply Fin.ext
  simp [rawFrontFin]

def rawReindexDerivative {n : ℕ} (e : ι ≃ Fin n)
    (D : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : ι => E) ℂ) :
    E →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin n => E) ℂ where
  toFun w := (D w).domDomCongr e
  map_add' w z := by ext v; simp [MultilinearMap.domDomCongr_apply]
  map_smul' r w := by ext v; simp [MultilinearMap.domDomCongr_apply]

omit [Fintype ι] [DecidableEq ι] in
lemma HasRawFDerivAt.reindex [Fintype ι] [DecidableEq ι] {n : ℕ} (e : ι ≃ Fin n)
    {a : E → MultilinearMap ℝ (fun _ : ι => E) ℂ}
    {D : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : ι => E) ℂ} {x : E}
    (ha : HasRawFDerivAt a D x) :
    HasRawFDerivAt (fun y => (a y).domDomCongr e) (rawReindexDerivative e D) x := by
  intro v
  exact ha (v ∘ e)

omit [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι] in
lemma rawPrefix_uncurry_reindex [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι] {n : ℕ} (e : ι ≃ Fin n)
    (D : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : ι => E) ℂ) :
    (rawPrefix D).domDomCongr ((Equiv.sumCongr (Equiv.refl (Fin 1)) e).trans (rawFrontFin n)) =
      (rawReindexDerivative e D).uncurryLeft := by
  ext v
  change D (v (rawFrontFin n (Sum.inl 0)))
      (fun i => v (rawFrontFin n (Sum.inr (e i)))) = D (v 0) (fun i => v (e i).succ)
  have h0 : rawFrontFin n (Sum.inl (0 : Fin 1)) = 0 := rawFrontFin_inl n 0
  have htail : (fun i => v (rawFrontFin n (Sum.inr (e i)))) = (fun i => v (e i).succ) :=
    funext (fun i => congrArg v (rawFrontFin_inr (e i)))
  rw [h0, htail]

/-- Exterior differentiation with an arbitrary explicit ordering of raw
slots, retaining the order of the distinguished derivative slot. -/
theorem extDeriv_of_reindexed_raw {n : ℕ} (e : ι ≃ Fin n)
    {a : E → MultilinearMap ℝ (fun _ : ι => E) ℂ}
    {D : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : ι => E) ℂ}
    {ω : E → E [⋀^Fin n]→L[ℝ] ℂ} {x : E}
    (hω : DifferentiableAt ℝ ω x)
    (heq : ∀ᶠ y in 𝓝 x, (ω y).toAlternatingMap = (a y).alternatization.domDomCongr e)
    (ha : HasRawFDerivAt a D x) :
    (extDeriv ω x).toAlternatingMap = (rawPrefix D).alternatization.domDomCongr
      ((Equiv.sumCongr (Equiv.refl (Fin 1)) e).trans (rawFrontFin n)) := by
  rw [← raw_alternatization_reindex, rawPrefix_uncurry_reindex]
  apply extDeriv_of_raw_alternatization hω _ (ha.reindex e)
  exact heq.mono (fun y hy => hy.trans (raw_alternatization_reindex (a y) e).symm)

end
end Mahler

end OAI
