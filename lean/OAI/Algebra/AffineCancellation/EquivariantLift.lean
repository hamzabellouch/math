import OAI.Algebra.AffineCancellation.TorsorEuler
import OAI.Algebra.AffineCancellation.BundleGrading

namespace OAI

noncomputable section

namespace ComplexCancellation.PolynomialTorsor
open PolynomialModel
lemma exists_equivariant_lift (D : Derivation ℂ Degeneration.G Degeneration.G)
    (hD : LND.LocallyNilpotent D) (hDn : D ≠ 0) :
    ∃ (c : Degeneration.G) (E : Derivation ℂ Bundle.B Bundle.B),
      c ≠ 0 ∧ LND.LocallyNilpotent E ∧ E ≠ 0 ∧
      (∀ r, E (Bundle.pullback r)=Bundle.pullback (c*D r)) ∧
      ∀ b, Bundle.fiberEuler (E b)=E (Bundle.fiberEuler b) := by
  obtain ⟨s,hs,hss⟩ := local_slice D hD hDn
  let t : K := ι (k := ℂ) s/ι (k := ℂ) (D s)
  have hi : Function.Injective (ι (k := ℂ) (R := Degeneration.G)) :=
    IsFractionRing.injective Degeneration.G K
  have hsn : ι (k := ℂ) (D s) ≠ 0 := by simpa only [map_zero] using hi.ne hs
  have ht : FractionDerivation.extend D t=1 := by
    change FractionDerivation.extend D (algebraMap Degeneration.G K s/algebraMap Degeneration.G K (D s))=1
    rw [Derivation.leibniz_div_const _ _ _ (by rw [FractionDerivation.extend_algebraMap,hss,map_zero]),
      FractionDerivation.extend_algebraMap,smul_eq_mul]
    exact inv_mul_cancel₀ hsn
  let φ := ρ D hD ht
  have hφ : Function.Injective φ := ρ_injective D hD ht
  obtain ⟨Q⟩ := exists_frame D hD ht
  have hf : Function.Injective (Torsor.forward φ Q) := forward_injective D hD ht Q
  let Dp : Derivation ℂ (P D) (P D) := SliceDerivative.derivation
  have hDp : LND.LocallyNilpotent Dp := SliceDerivative.locallyNilpotent
  have hder (r : Degeneration.G) : Dp (φ r)=φ (D r) := derivative_model D hD ht r
  have hc (p : P D) : p ∈ InvariantClearing.subalgebra φ D :=
    clear_polynomial D hD ht s hs hss rfl p
  obtain ⟨c,E,hDc,hcn,hE,hsE⟩ := Torsor.invariant_replica φ Q D hφ hc Dp hDp hder hf
  have hbase (r : Degeneration.G) : Torsor.forward φ Q (Bundle.pullback r)=Torsor.base φ r :=
    DFunLike.congr_fun (Torsor.forward_pullback φ Q hφ) r
  have he (r : Degeneration.G) : E (Bundle.pullback r)=Bundle.pullback (c*D r) := by
    apply hf
    rw [hsE,hbase,Torsor.extension_base φ D Dp hder,hbase,map_mul]
  have hEn : E ≠ 0 := by
    intro hz
    apply hDn
    ext r
    have h := he r
    rw [hz,Derivation.zero_apply] at h
    have hz' : c*D r=0 := Bundle.pullback_injective (by simpa only [map_zero] using h.symm)
    exact (mul_eq_zero.mp hz').resolve_left hcn
  exact ⟨c,E,hcn,hE,hEn,he,Torsor.replica_commute φ Q hφ hf Dp E c hsE⟩
end ComplexCancellation.PolynomialTorsor

end

end OAI
