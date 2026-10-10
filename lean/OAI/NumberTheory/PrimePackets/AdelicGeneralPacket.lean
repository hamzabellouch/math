import Mathlib
import OAI.NumberTheory.PrimePackets.AdelicDiagonalizer
import OAI.NumberTheory.PrimePackets.AdelicGeneralPacketDefinitions

namespace OAI

noncomputable section
open scoped TensorProduct Topology MatrixGroups
open Matrix Module Set MeasureTheory
namespace PrimeDegreePackets.Adelic

lemma diagonal_translate_base {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K) (σ : OrderedEmbeddings n K)
    (g : GL (Fin n) RationalFiniteAdeles) (z : (Fin n → ℝ)ˣ) :
    adelicRegular b ((ideleEquiv σ hn).symm (z,1)) *
      (ProjGenLinGroup.mk (realBasisGL hn b σ),ProjGenLinGroup.mk g) =
      (ProjGenLinGroup.mk (realBasisGL hn b σ * diagonalUnits n z),ProjGenLinGroup.mk g) := by
  rw [adelicRegular_translate,(ideleEquiv σ hn).apply_symm_apply]
  simp

theorem general_adelic_packet_identification {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (hodd : Odd (d+1)) (hn : finrank ℚ K = d+1)
    (b : Basis (Fin (d+1)) ℚ K) (h : PGL(Fin (d+1), ℝ))
    (hh : AllowedRealDiagonalizer b h) (g : GL (Fin (d+1)) RationalFiniteAdeles) :
    ∃ σ : OrderedEmbeddings (d+1) K, ∃ p : C(TorusQuotient K, X (d+1)),
      (∀ t : (TensorAdeles K)ˣ, ambientEquiv hodd hn b (p (QuotientGroup.mk t)) =
        generalAdelicOrbit b h g t) ∧
      Set.range p = packetSupport (matrixFullLattice hn b g) σ ∧
      ∀ ν : Measure (TorusQuotient K), IsProbabilityMeasure ν → Measure.IsMulLeftInvariant ν →
        Measure.map p ν = packetMeasure (matrixFullLattice hn b g) σ := by
  obtain ⟨σ,z,rfl⟩ := allowed_real_diagonalizer_factorization hn b h hh
  let u := (ideleEquiv σ hn).symm (z,1)
  let a : TorusQuotient K := QuotientGroup.mk u
  let p₀ := adelicTorusPoint hodd hn b σ g
  have hp₀ : Continuous p₀ := continuous_adelicTorusPoint hodd hn b σ g
  let p : C(TorusQuotient K, X (d+1)) := ⟨fun q => p₀ (q*a),hp₀.comp (continuous_id.mul_const a)⟩
  refine ⟨σ,p,?_,?_,?_⟩
  · intro t
    change ambientEquiv hodd hn b (adelicTorusPoint hodd hn b σ g (QuotientGroup.mk (t*u))) = _
    change ambientEquiv hodd hn b ((ambientEquiv hodd hn b).symm _) = _
    rw [Equiv.apply_symm_apply]
    change DoubleCoset.mk _ _ (adelicRegular b (t*u) * _) = _
    rw [map_mul,mul_assoc,diagonal_translate_base]
    rfl
  · rw [← range_adelicTorusPoint hodd hn b σ g]
    ext x
    constructor
    · rintro ⟨q,rfl⟩
      exact ⟨q*a,rfl⟩
    · rintro ⟨q,rfl⟩
      refine ⟨q*a⁻¹,?_⟩
      change p₀ (q*a⁻¹*a) = p₀ q
      simp [mul_assoc]
  · intro ν hν hInv
    let := hν
    let := hInv
    have hmap : Measure.map p ν = Measure.map p₀ ν := by
      change Measure.map (p₀ ∘ (fun q => q*a)) ν = _
      have hm : Measurable (fun q : TorusQuotient K => q*a) :=
        (continuous_id.mul_const a).measurable
      calc Measure.map (p₀ ∘ (fun q => q*a)) ν =
            Measure.map p₀ (Measure.map (fun q => q*a) ν) := (Measure.map_map hp₀.measurable hm).symm
        _ = Measure.map p₀ ν := congrArg (Measure.map p₀) (map_mul_right_eq_self ν a)
    rw [hmap]
    exact (adelicParametrization hodd hn b σ g).map_invariant_probability hn hodd ν

end PrimeDegreePackets.Adelic

end

end OAI
