import OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAmpleDimension
import OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

def topEuler (p : X ⟶ Spec (CommRingCat.of ℂ)) (d : ℕ) (L : LineBundle X) : ℤ :=
  (fwdDiff (1 : ℕ))^[d] (fun n => eulerCharacteristic p d (L.pow n).sheaf) 0

def mixedEuler (p : X ⟶ Spec (CommRingCat.of ℂ)) (d : ℕ)
    (ls : List (LineBundle X)) : ℤ := mixedTop (lineEuler p d) ls

theorem mixedEuler_replicate (p : X ⟶ Spec (CommRingCat.of ℂ)) (d : ℕ)
    (L : LineBundle X) : mixedEuler p d (List.replicate d L) = topEuler p d L :=
  mixedTop_replicate L _ (lineEuler_isoInvariant p d) d

theorem mixedEuler_perm (p : X ⟶ Spec (CommRingCat.of ℂ)) (d : ℕ)
    {ls ks : List (LineBundle X)} (h : ls.Perm ks) :
    mixedEuler p d ls = mixedEuler p d ks :=
  congrFun (mixedDifference_perm h _ (lineEuler_isoInvariant p d)) (structureLineBundle X)

theorem lineEuler_mixedDegreeLE [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d) : MixedDegreeLE d (lineEuler p d) :=
  mixedDifference_lineEuler_of_ample p H hH d hdim

theorem mixedEuler_tensor_cons [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d)
    (A B : LineBundle X) (ls : List (LineBundle X)) (hlen : ls.length+1=d) :
    mixedEuler p d (A.tensor B :: ls) = mixedEuler p d (A :: ls) + mixedEuler p d (B :: ls) :=
  congrFun (mixedDifference_tensor_cons_of_degree (lineEuler_isoInvariant p d)
    (lineEuler_mixedDegreeLE p H hH d hdim) A B ls hlen) (structureLineBundle X)

theorem topEuler_pow [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d) (L : LineBundle X) (n : ℕ) :
    topEuler p d (L.pow n) = (n : ℤ)^d * topEuler p d L := by
  rw [← mixedEuler_replicate p d (L.pow n), ← mixedEuler_replicate p d L]
  have he := mixedTop_two_powers (lineEuler_isoInvariant p d)
    (lineEuler_mixedDegreeLE p H hH d hdim) L L n 0 d 0 (by omega)
  simpa only [List.replicate_zero, List.append_nil, pow_zero, mul_one, mixedEuler] using he

theorem topEuler_tensor_powers_binomial [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d) (A B : LineBundle X) (a b : ℕ) :
    topEuler p d ((A.pow a).tensor (B.pow b)) =
      ∑ k ∈ Finset.range (d+1), (d.choose k : ℤ) * (a : ℤ)^k * (b : ℤ)^(d-k) *
        mixedEuler p d (List.replicate k A ++ List.replicate (d-k) B) := by
  rw [← mixedEuler_replicate]
  exact mixedTop_tensor_powers_binomial (lineEuler_isoInvariant p d)
    (lineEuler_mixedDegreeLE p H hH d hdim) A B a b

theorem mixedEuler_tensor_powers_binomial_append [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d) (A B : LineBundle X) (a b n : ℕ)
    (ls : List (LineBundle X)) (hlen : n+ls.length=d) :
    mixedEuler p d (List.replicate n ((A.pow a).tensor (B.pow b)) ++ ls) =
      ∑ k ∈ Finset.range (n+1), (n.choose k : ℤ) * (a : ℤ)^k * (b : ℤ)^(n-k) *
        mixedEuler p d (List.replicate k A ++ List.replicate (n-k) B ++ ls) :=
  mixedTop_tensor_powers_binomial_append (lineEuler_isoInvariant p d)
    (lineEuler_mixedDegreeLE p H hH d hdim) A B a b n ls hlen

end
end PiExponent.NumericalAmpleness

end OAI
