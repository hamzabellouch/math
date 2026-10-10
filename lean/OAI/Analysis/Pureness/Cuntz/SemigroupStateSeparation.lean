import OAI.Analysis.Pureness.Cuntz.SemigroupGrothendieck
import OAI.Analysis.Pureness.Cuntz.RationalizedCone
import OAI.Analysis.Pureness.Cuntz.SemigroupStates

namespace OAI
noncomputable section
namespace CuntzPureness.OrderedSemigroup
open Algebra
open scoped ENNReal
variable {S : Type*} [AddCommMonoid S] [PartialOrder S] [IsOrderedAddMonoid S]

abbrev semigroupRationalMap : S →+ RationalGroup (GrothendieckAddGroup S) :=
  (toRationalGroup (GrothendieckAddGroup S)).toAddMonoidHom.comp GrothendieckAddGroup.of

abbrev semigroupRationalCone : PointedCone ℚ (RationalGroup (GrothendieckAddGroup S)) :=
  rationalCone (grothendieckCone (S := S))

def stateOfRationalPositive (hzero : ∀ a : S, 0 ≤ a) (u : S)
    (f : RationalGroup (GrothendieckAddGroup S) →ₗ[ℚ] ℝ)
    (hfu : f (semigroupRationalMap u) = 1)
    (hf : ∀ z ∈ semigroupRationalCone, 0 ≤ f z) : StateSpace u := by
  have hpos : ∀ a : S, 0 ≤ f (semigroupRationalMap a) := fun a =>
    hf _ (rationalCone_of_mem _ (grothendieck_of_nonneg hzero a))
  refine ⟨fun a => ENNReal.ofReal (f (semigroupRationalMap a)), ?_, ?_, ?_, ?_⟩
  · simp
  · intro a b
    simp only [map_add]
    exact ENNReal.ofReal_add (hpos a) (hpos b)
  · intro a b hab
    apply ENNReal.ofReal_le_ofReal
    have h := hf _ (rationalCone_of_mem (grothendieckCone (S := S)) ⟨a,b,hab,rfl⟩)
    simp only [map_sub, sub_nonneg] at h
    dsimp [semigroupRationalMap] at h ⊢
    exact h
  · change ENNReal.ofReal (f (semigroupRationalMap u)) = 1
    rw [hfu, ENNReal.ofReal_one]

theorem exists_strict_buffer_of_states (hzero : ∀ a : S, 0 ≤ a)
    (u x : S) (hunit : ∀ a : S, ∃ n : ℕ, a ≤ n • u)
    (hgap : ∀ f : StateSpace u, f.1 x < 1) :
    ∃ m n : ℕ, m < n ∧ ∃ c : S, n • x+c ≤ m • u+c := by
  let C := semigroupRationalCone (S := S)
  let U := semigroupRationalMap u
  let X := semigroupRationalMap x
  have hU : U ∈ C := rationalCone_of_mem _ (grothendieck_of_nonneg hzero u)
  have hbound : ∀ z, ∃ r : ℚ, r • U+z ∈ C :=
    rationalCone_orderUnit _ _ (grothendieck_orderUnit hzero u hunit)
  obtain ⟨q,hq,hqx⟩ := RationalRiesz.strict_bound_of_states C U X hU hbound (by
    intro f hfu hf
    have h := hgap (stateOfRationalPositive hzero u f hfu hf)
    change ENNReal.ofReal (f X) < 1 at h
    have hh : ENNReal.ofReal (f X) < ENNReal.ofReal 1 := by simpa using h
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mp hh)
  have hex : ∃ q : ℚ, 0 ≤ q ∧ q < 1 ∧ q • U-X ∈ C := by
    by_cases hq0 : 0 ≤ q
    · exact ⟨q,hq0,hq,hqx⟩
    · refine ⟨0,le_rfl,by norm_num,?_⟩
      have h := C.add_mem (C.smul_mem (neg_nonneg.mpr (le_of_not_ge hq0)) hU) hqx
      have heq : (-q) • U + (q • U-X) = (0 : ℚ) • U-X := by
        rw [neg_smul,zero_smul]
        abel
      exact heq ▸ h
  obtain ⟨q,hq0,hq,hqx⟩ := hex
  let p := q.num.toNat
  let d := q.den
  have hd : 0 < d := q.den_pos
  have hdp : (d : ℚ)*q = p := rational_nat_mul q hq0
  have hpd : p < d := by
    have h := mul_lt_mul_of_pos_left hq (show (0 : ℚ) < d by exact_mod_cast hd)
    rw [hdp,mul_one] at h
    exact_mod_cast h
  have hmem := C.smul_mem (show (0 : ℚ) ≤ d by positivity) hqx
  have heq : (d : ℚ) • (q • U-X) =
      toRationalGroup (GrothendieckAddGroup S)
        (p • GrothendieckAddGroup.of u-d • GrothendieckAddGroup.of x) := by
    rw [smul_sub,smul_smul,hdp,map_sub,map_nsmul,map_nsmul]
    simp only [Nat.cast_smul_eq_nsmul]
    rfl
  rw [heq] at hmem
  obtain ⟨k,hk,hkP⟩ := (rationalCone_of_iff (grothendieckCone (S := S)) _).mp hmem
  have heq2 : k • (p • GrothendieckAddGroup.of u-d • GrothendieckAddGroup.of x) =
      GrothendieckAddGroup.of ((k*p) • u)-GrothendieckAddGroup.of ((k*d) • x) := by
    simp only [smul_sub,map_nsmul,mul_nsmul]
    congr 1 <;> exact smul_comm _ _ _
  rw [heq2] at hkP
  obtain ⟨c,hc⟩ := (grothendieck_mem_cone_iff ((k*d) • x) ((k*p) • u)).mp hkP
  exact ⟨k*p,k*d,Nat.mul_lt_mul_of_pos_left hpd hk,c,hc⟩

theorem le_of_states (hzero : ∀ a : S, 0 ≤ a)
    (hAU : ∀ a b : S, ∀ k : ℕ, 1 ≤ k → (k+1) • a ≤ k • b → a ≤ b)
    (u x : S) (hunit : ∀ a : S, ∃ n : ℕ, a ≤ n • u)
    (hgap : ∀ f : StateSpace u, f.1 x < 1) : x ≤ u := by
  obtain ⟨m,n,hmn,c,hc⟩ := exists_strict_buffer_of_states hzero u x hunit hgap
  obtain ⟨k,hk⟩ := hunit c
  exact strict_multiples_le_of_buffer hzero hAU hmn hc hk
end CuntzPureness.OrderedSemigroup

end

end OAI
