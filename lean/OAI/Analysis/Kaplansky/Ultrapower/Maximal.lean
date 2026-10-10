import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.Ultrapower.UltraSaturation
import OAI.Analysis.Kaplansky.Ultrapower.PartialIsometry

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue

open Filter Topology
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]
variable (V : QuasiValue A) (u : Ultrafilter ℕ) (hu : (u : Filter ℕ) ≤ atTop)

include hu in
lemma ultra_maximal_extension {v : V.UltraQuotient u} (hv : IsPartialIsometry v) :
    ∃ w : V.UltraQuotient u, IsPartialIsometry w ∧ w*(star v*v)=v ∧
      ∀ z : V.UltraQuotient u, IsPartialIsometry z → z*(star v*v)=v →
        V.ultraQ u z ≤ V.ultraQ u w := by
  let W := V.ultra u
  let s : Set ℝ := {r | ∃ z : V.UltraQuotient u, IsPartialIsometry z ∧ z*(star v*v)=v ∧ V.ultraQ u z=r}
  have hs : s.Nonempty := ⟨V.ultraQ u v,v,hv,hv.mul_initial,rfl⟩
  have hb : BddAbove s := by
    refine ⟨1,?_⟩
    rintro r ⟨z,hz,_,rfl⟩
    have hn := hz.norm_le
    have hq := W.quotQ_bound z
    nlinarith [norm_nonneg z]
  let S := sSup s
  let t : StarTerm (V.UltraQuotient u) := .var
  let sub (a b : StarTerm (V.UltraQuotient u)) := StarTerm.add a (.neg b)
  let P : Fin 3 → StarTerm (V.UltraQuotient u) :=
    ![sub (.mul (.mul t (.star t)) t) t,
      sub (.mul t (.const (star v*v))) (.const v),t]
  let R : Fin 3 → ℝ := ![0,0,S]
  have happ (ε : ℝ) (hε : 0<ε) : ∃ z : V.UltraQuotient u,
      ‖z‖ ≤ 1 ∧ ∀ j : Fin 3, |V.ultraQ u ((P j).eval id z)-R j| < ε := by
    obtain ⟨r,hr,hlt⟩ := exists_lt_of_lt_csSup hs (sub_lt_self S hε)
    obtain ⟨z,hz,hzv,rfl⟩ := hr
    have hle : V.ultraQ u z≤S := le_csSup hb ⟨z,hz,hzv,rfl⟩
    refine ⟨z,hz.norm_le,?_⟩
    intro j
    fin_cases j <;> simp [P,R,sub,t,StarTerm.eval,← sub_eq_add_neg]
    · change |W.quotQ (z*star z*z-z)| < ε
      rw [show z*star z*z=z from hz,sub_self,W.quotQ_zero,abs_zero]
      exact hε
    · change |W.quotQ (z*(star v*v)-v)| < ε
      rw [hzv,sub_self,W.quotQ_zero,abs_zero]
      exact hε
    · rw [abs_of_nonpos (sub_nonpos.mpr hle)]
      linarith
  obtain ⟨w,hw⟩ := V.ultra_realize u hu P R happ
  have h0 := hw 0
  have h1 := hw 1
  have h2 := hw 2
  simp [P,R,sub,t,StarTerm.eval,← sub_eq_add_neg] at h0 h1 h2
  have hw0 : IsPartialIsometry w := sub_eq_zero.mp ((W.quotQ_eq_zero _).mp h0)
  have hw1 : w*(star v*v)=v := sub_eq_zero.mp ((W.quotQ_eq_zero _).mp h1)
  refine ⟨w,hw0,hw1,?_⟩
  intro z hz hzv
  rw [h2]
  exact le_csSup hb ⟨z,hz,hzv,rfl⟩


end KaplanskyConsequences.QuasiValue

end

end OAI
