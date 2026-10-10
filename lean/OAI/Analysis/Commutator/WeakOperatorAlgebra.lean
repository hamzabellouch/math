import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace Topology

open Filter

namespace Kadison.WeakOperatorLimit

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {l : Filter ι} [l.NeBot] {T : ι → H →L[ℂ] H} {W : H →L[ℂ] H}

variable (hlim : ∀ x y, Tendsto (fun i => inner ℂ (T i x) y) l (𝓝 (inner ℂ (W x) y)))

include hlim

omit [CompleteSpace H] in
lemma right_eq (A B : H →L[ℂ] H) (h : ∀ᶠ i in l, T i*A=B) : W*A=B := by
  ext x
  apply ext_inner_right ℂ
  intro y
  exact tendsto_nhds_unique (hlim (A x) y) (tendsto_const_nhds.congr' (by
    filter_upwards [h] with i hi
    exact congrArg (fun U : H →L[ℂ] H => inner ℂ (U x) y) hi.symm))

lemma intertwine (A B : H →L[ℂ] H) (h : ∀ᶠ i in l, T i*A=B*T i) : W*A=B*W := by
  ext x
  apply ext_inner_right ℂ
  intro y
  have he : ∀ᶠ i in l, inner ℂ (T i (A x)) y=inner ℂ (T i x) (star B y) := by
    filter_upwards [h] with i hi
    rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
    exact congrArg (fun U : H →L[ℂ] H => inner ℂ (U x) y) hi
  have hl := (hlim x (star B y)).congr' (he.mono fun _ hi => hi.symm)
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right] at hl
  exact tendsto_nhds_unique (hlim (A x) y) hl

lemma mem_vonNeumann (M : VonNeumannAlgebra H) (hM : ∀ᶠ i in l, T i∈M) : W∈M := by
  change W∈M.carrier
  rw [←M.centralizer_centralizer']
  intro a ha
  exact (intertwine hlim a a (hM.mono fun i hi => ha (T i) hi)).symm

end Kadison.WeakOperatorLimit

end

end
end

end OAI
