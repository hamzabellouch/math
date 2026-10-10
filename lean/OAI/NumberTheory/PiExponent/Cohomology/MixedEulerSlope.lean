import OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra
import OAI.NumberTheory.PiExponent.Cohomology.MixedEulerTop
import OAI.NumberTheory.PiExponent.Polynomials.MixedSlopePolynomial

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

def eulerSlopeCoefficient (p : X ⟶ Spec (CommRingCat.of ℂ)) (d : ℕ)
    (L H : LineBundle X) (k : ℕ) : ℝ :=
  mixedEuler p d (List.replicate k H ++ List.replicate (d-k) L)

def eulerSlopePolynomial (p : X ⟶ Spec (CommRingCat.of ℂ)) (d : ℕ)
    (L H : LineBundle X) : Polynomial ℝ :=
  mixedSlopePolynomial d (eulerSlopeCoefficient p d L H)

theorem topEuler_iso (p : X ⟶ Spec (CommRingCat.of ℂ)) (d : ℕ)
    (L M : LineBundle X) (e : L.sheaf ≅ M.sheaf) : topEuler p d L = topEuler p d M := by
  have he : (fun n => eulerCharacteristic p d (L.pow n).sheaf) =
      fun n => eulerCharacteristic p d (M.pow n).sheaf := by
    funext n
    exact eulerCharacteristic_iso p ((modulePowFunctor n).mapIso e) d
  unfold topEuler
  rw [he]

theorem mixedEuler_replicate_iso_append (p : X ⟶ Spec (CommRingCat.of ℂ)) (d : ℕ)
    (L M : LineBundle X) (e : L.sheaf ≅ M.sheaf) (n : ℕ) (ls : List (LineBundle X)) :
    mixedEuler p d (List.replicate n L ++ ls) =
      mixedEuler p d (List.replicate n M ++ ls) := by
  have he : mixedDifference (List.replicate n L ++ ls) (lineEuler p d) =
      mixedDifference (List.replicate n M ++ ls) (lineEuler p d) := by
    induction n with
    | zero => rfl
    | succ n ih =>
        simp only [List.replicate_succ, List.cons_append]
        rw [mixedDifference_iso_cons L M e _ _ (lineEuler_isoInvariant p d)]
        exact congrArg (tensorDifference M) ih
  exact congrFun he (structureLineBundle X)

theorem eulerSlopePolynomial_natDegree_le (p : X ⟶ Spec (CommRingCat.of ℂ)) (d : ℕ)
    (L H : LineBundle X) : (eulerSlopePolynomial p d L H).natDegree ≤ d :=
  mixedSlopePolynomial_natDegree_le d _

theorem eulerSlopePolynomial_eval_zero (p : X ⟶ Spec (CommRingCat.of ℂ)) (d : ℕ)
    (L H : LineBundle X) : (eulerSlopePolynomial p d L H).eval 0 = (topEuler p d L : ℝ) := by
  rw [eulerSlopePolynomial, mixedSlopePolynomial_eval_zero]
  simp only [eulerSlopeCoefficient, List.replicate_zero, Nat.sub_zero, List.nil_append,
    mixedEuler_replicate]

theorem topEuler_slopeBundle_eq [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (L : LineBundle X) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d) (a b : ℕ) (hb : 0 < b) :
    (topEuler p d (slopeBundle L H a b) : ℝ) =
      (b : ℝ)^d * (eulerSlopePolynomial p d L H).eval ((a : ℝ)/b) := by
  have he := topEuler_iso p d (slopeBundle L H a b) ((H.pow a).tensor (L.pow b))
    (moduleTensorComm (L.pow b).sheaf (H.pow a).sheaf)
  rw [he, topEuler_tensor_powers_binomial p H hH d hdim H L a b,
    eulerSlopePolynomial, mixedSlopePolynomial_eval_div d _ _ _ (by exact_mod_cast (Nat.ne_of_gt hb))]
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  dsimp only [eulerSlopeCoefficient]
  ring

theorem mixedEuler_slopeBundle_eq_append [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (L : LineBundle X) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d) (a b n : ℕ) (hb : 0 < b)
    (ls : List (LineBundle X)) (hlen : n+ls.length=d) :
    (mixedEuler p d (List.replicate n (slopeBundle L H a b) ++ ls) : ℝ) =
      (b : ℝ)^n * (mixedSlopePolynomial n (fun k =>
        (mixedEuler p d (List.replicate k H ++ List.replicate (n-k) L ++ ls) : ℝ))).eval
          ((a : ℝ)/b) := by
  rw [mixedEuler_replicate_iso_append p d (slopeBundle L H a b)
      ((H.pow a).tensor (L.pow b))
      (moduleTensorComm (L.pow b).sheaf (H.pow a).sheaf),
    mixedEuler_tensor_powers_binomial_append p H hH d hdim H L a b n ls hlen,
    mixedSlopePolynomial_eval_div n _ _ _ (by exact_mod_cast (Nat.ne_of_gt hb))]
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem eulerSlopeCoefficient_succ (p : X ⟶ Spec (CommRingCat.of ℂ)) (d : ℕ)
    (L H : LineBundle X) (k : ℕ) :
    eulerSlopeCoefficient p (d+1) L H (k+1) =
      (mixedEuler p (d+1) (List.replicate k H ++ List.replicate (d-k) L ++ [H]) : ℝ) := by
  dsimp only [eulerSlopeCoefficient]
  congr 1
  apply mixedEuler_perm
  simpa only [List.replicate_succ, List.cons_append, Nat.add_sub_add_right,
    List.append_nil] using
    (List.perm_middle (a := H)
      (l₁ := List.replicate k H ++ List.replicate (d-k) L) (l₂ := [])).symm

theorem eulerSlopePolynomial_derivative_eval_nat_div [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (L : LineBundle X) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1) (a b : ℕ) (hb : 0 < b) :
    (b : ℝ)^d * (eulerSlopePolynomial p (d+1) L H).derivative.eval ((a : ℝ)/b) =
      (d+1 : ℕ) *
        (mixedEuler p (d+1) (H :: List.replicate d (slopeBundle L H a b)) : ℝ) := by
  rw [eulerSlopePolynomial, mixedSlopePolynomial_derivative_eval]
  have hc : (fun k => eulerSlopeCoefficient p (d+1) L H (k+1)) =
      fun k => (mixedEuler p (d+1)
        (List.replicate k H ++ List.replicate (d-k) L ++ [H]) : ℝ) := by
    funext k
    exact eulerSlopeCoefficient_succ p d L H k
  rw [hc]
  have he := mixedEuler_slopeBundle_eq_append p H hH L (d+1)
    (by simpa only [Nat.cast_add, Nat.cast_one] using hdim) a b d hb [H] (by simp)
  have hp : mixedEuler p (d+1) (List.replicate d (slopeBundle L H a b) ++ [H]) =
      mixedEuler p (d+1) (H :: List.replicate d (slopeBundle L H a b)) := by
    apply mixedEuler_perm
    simpa only [List.append_nil] using
      (List.perm_middle (a := H) (l₁ := List.replicate d (slopeBundle L H a b)) (l₂ := []))
  rw [hp] at he
  calc
    _ = (d+1 : ℕ) * ((b : ℝ)^d * (mixedSlopePolynomial d (fun k =>
        (mixedEuler p (d+1) (List.replicate k H ++ List.replicate (d-k) L ++ [H]) : ℝ))).eval
          ((a : ℝ)/b)) := by ring
    _ = _ := by rw [← he]

theorem mixedEuler_pow_cons [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d) (L : LineBundle X) (n : ℕ)
    (ls : List (LineBundle X)) (hlen : ls.length+1=d) :
    mixedEuler p d (L.pow n :: ls) = (n : ℤ) * mixedEuler p d (L :: ls) := by
  have he := congrFun (mixedDifference_pow_cons_of_degree (lineEuler_isoInvariant p d)
    (lineEuler_mixedDegreeLE p H hH d hdim) L n ls hlen) (structureLineBundle X)
  simpa only [mixedEuler, mixedTop, Pi.smul_apply, nsmul_eq_mul,
    Pi.mul_apply, Pi.natCast_apply] using he

theorem topEuler_slopeBundle_split [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (L : LineBundle X) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1) (a b : ℕ) :
    topEuler p (d+1) (slopeBundle L H a b) =
      (b : ℤ) * mixedEuler p (d+1) (L :: List.replicate d (slopeBundle L H a b)) +
      (a : ℤ) * mixedEuler p (d+1) (H :: List.replicate d (slopeBundle L H a b)) := by
  have hd : topologicalKrullDim X ≤ ((d+1 : ℕ) : WithBot ℕ∞) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hdim
  rw [← mixedEuler_replicate p (d+1), List.replicate_succ]
  change mixedEuler p (d+1) (((L.pow b).tensor (H.pow a)) ::
    List.replicate d (slopeBundle L H a b)) = _
  rw [mixedEuler_tensor_cons p H hH (d+1) hd _ _ _ (by simp),
    mixedEuler_pow_cons p H hH (d+1) hd L b _ (by simp),
    mixedEuler_pow_cons p H hH (d+1) hd H a _ (by simp)]

end
end PiExponent.NumericalAmpleness

end OAI
