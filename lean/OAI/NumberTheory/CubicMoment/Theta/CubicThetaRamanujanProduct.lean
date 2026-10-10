import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamanujan
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticVoronoi

namespace OAI

/-! The actual finite Ramanujan average is precisely the squarefree local
Euler coefficient in the published Voronoi formula. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaRamanujan_prod (s : Finset Eisenstein)
    (hp : ∀ p∈s,primaryPrime p) (h : Eisenstein) :
    cubicThetaRamanujan (∏ p∈s,p) h=
      ∏ p∈s,if p∣h then (norm p:ℂ)-1 else -1 := by
  induction s using Finset.induction_on with
  | empty => simp [cubicThetaRamanujan_one]
  | @insert p s hps ih =>
    have hp' := hp p (Finset.mem_insert_self _ _)
    have hs : ∀ q∈s,primaryPrime q := fun q hq => hp q (Finset.mem_insert_of_mem hq)
    have hprimary := primary_finset_prod s (fun q => q) (fun q hq => (hs q hq).1)
    have hc : IsCoprime p (∏ q∈s,q) := by
      apply IsCoprime.prod_right
      intro q hq
      exact primaryPrimes_isCoprime hp' (hs q hq) (fun heq => hps (heq ▸ hq))
    rw [Finset.prod_insert hps,cubicThetaRamanujan_mul hp'.1 hprimary hc,
      cubicThetaRamanujan_prime hp',ih hs,Finset.prod_insert hps]

theorem cubicThetaRamanujan_squarefree {r : Eisenstein} (hr : primary r)
    (hs : Squarefree r) (n : MetaplecticDualArgument) :
    cubicThetaRamanujan r n.val=metaplecticLocalCoefficient r n := by
  calc
    _ = ∏ p∈primaryPrimeFactors r,if p∣n.val then (norm p:ℂ)-1 else -1 := by
      conv_lhs => rw [←primaryPrimeFactors_prod hr hs]
      exact cubicThetaRamanujan_prod _ (fun p hp => (primaryPrimeFactor_spec hr hp).1) n.val
    _ = _ := by
      unfold metaplecticLocalCoefficient
      apply Finset.prod_congr rfl
      intro p _
      split_ifs <;> push_cast <;> rfl

lemma cubicTheta_sum_eq_units {R : Type*} [CommRing R] [Fintype R]
    (f : R→ℂ) (hf : ∀ x,¬IsUnit x→f x=0) :
    (∑ x : R,f x)=∑ u : Rˣ,f u := by
  have hs : Function.support f ⊆ {x | IsUnit x} := by
    intro x hx
    by_contra hu
    exact hx (hf x hu)
  let e := (Submonoid.unitsTypeEquivIsUnitSubmonoid (M:=R)).toEquiv
  calc
    _ = ∑' x : R,f x := (tsum_fintype _).symm
    _ = ∑' x : {x : R // IsUnit x},f x := (tsum_subtype_eq_of_support_subset hs).symm
    _ = ∑' u : Rˣ,f u := (e.tsum_eq (fun x => f x.val)).symm
    _ = _ := tsum_fintype _

theorem cubicThetaRamanujan_units {r : Eisenstein} (hr : primary r)
    [Fintype (Residues r)] (h : Eisenstein) :
    cubicThetaRamanujan r h=
      ∑ u : (Residues r)ˣ,additivePhase r (h*residueRepresentative r u) := by
  rw [cubicThetaRamanujan,tsum_fintype]
  have hz (x : Residues r) (hx : ¬IsUnit x) :
      cubicSymbol r (residueRepresentative r x)^3*additivePhase r (h*residueRepresentative r x)=0 := by
    have hn : ¬IsCoprime r (residueRepresentative r x) := by
      intro hh
      exact hx (by simpa only [residueRepresentative_spec] using residue_isUnit_of_isCoprime hh)
    rw [cubicThetaSymbol_cube_indicator hr,ite_eq_right hn,zero_mul]
  rw [cubicTheta_sum_eq_units _ hz]
  apply Finset.sum_congr rfl
  intro u _
  have hu : IsCoprime r (residueRepresentative r u) := by
    apply isCoprime_of_residue_isUnit
    rw [residueRepresentative_spec]
    exact u.isUnit
  rw [cubicThetaSymbol_cube_indicator hr,ite_eq_left hu,one_mul]

end CubicFirstMoment

end

end OAI
