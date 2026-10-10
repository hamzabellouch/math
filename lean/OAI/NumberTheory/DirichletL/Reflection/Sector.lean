import OAI.NumberTheory.DirichletL.Reflection.Split

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem separate_product_congruence {A : Type*} [CommRing A]
    (M f r r₀ P P₀ : A) (hr : M^2 ∣ r-r₀) (hP : M^2 ∣ P-P₀) :
    M^2 ∣ f*r*P-f*r₀*P₀ := by
  have h := dvd_add (dvd_mul_of_dvd_left hr P) (dvd_mul_of_dvd_right hP r₀)
  convert dvd_mul_of_dvd_right h f using 1 ; ring

def separateSector (M r P : Eis) :
    (Eis ⧸ Ideal.span {M^2}) × (Eis ⧸ Ideal.span {M^2}) :=
  (Ideal.Quotient.mk _ r, Ideal.Quotient.mk _ P)

theorem separateSector_product (M f r r₀ P P₀ : Eis)
    (h : separateSector M r P = separateSector M r₀ P₀) :
    M^2 ∣ f*r*P-f*r₀*P₀ := by
  apply separate_product_congruence
  · exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (congrArg Prod.fst h))
  · exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (congrArg Prod.snd h))

theorem separate_numerator_congruence {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M a c l f r r₀ P P₀ : Eis) (p h : ι → Eis) (p₀ h₀ : κ → Eis)
    (hc : c ∣ M) (hh : ∀ i, M^2 ∣ h i) (hh₀ : ∀ i, M^2 ∣ h₀ i)
    (hp : (∏ i, p i) = f*r*P) (hp₀ : (∏ i, p₀ i) = f*r₀*P₀)
    (hs : separateSector M r P = separateSector M r₀ P₀) :
    M*c ∣ ShortDraftCRT.finiteCrossNumerator a c l p h -
      ShortDraftCRT.finiteCrossNumerator a c l p₀ h₀ := by
  apply ShortDraftCRT.finiteCrossNumerator_fixed_sector M a c l p h p₀ h₀ hc hh hh₀
  rw [hp,hp₀]
  exact separateSector_product M f r r₀ P P₀ hs

theorem controlled_bad_phase_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    {p : ι → Eis} {p₀ : κ → Eis} {N a c : Eis} {mode : Bool}
    (D : ControlledStratumArithmetic p N a c mode)
    (D₀ : ControlledStratumArithmetic p₀ N a c mode) (hc : c ≠ 0)
    (hbad : ramifiedTraceLambda^3*c ∣ N)
    (hr : N ∣ (∏ i, p i)-(∏ i, p₀ i))
    (hd : N ∣ D.matrix (fun _ => 1) 1 1 - D₀.matrix (fun _ => 1) 1 1) :
    ShortDraftCusp.A4BadPhase c hc (D.matrix (fun _ => 1) 1 1) D.U =
      ShortDraftCusp.A4BadPhase c hc (D₀.matrix (fun _ => 1) 1 1) D₀.U := by
  have hu : ramifiedTraceLambda^3*c ∣ D.U*(∏ i, p i)-1 := by
    refine ⟨-D.w, ?_⟩
    linear_combination D.bezout
  have hu₀ : ramifiedTraceLambda^3*c ∣ D₀.U*(∏ i, p₀ i)-1 := by
    refine ⟨-D₀.w, ?_⟩
    linear_combination D₀.bezout
  have hcop : IsCoprime (ramifiedTraceLambda^3*c) (∏ i, p i) := by
    refine ⟨D.w,D.U,?_⟩
    linear_combination D.bezout
  have he := ShortDraftCRT.inverse_weight_residue_congr
    (ramifiedTraceLambda^3*c) (∏ i, p i) (∏ i, p₀ i) D.U D₀.U
    (D.matrix (fun _ => 1) 1 1) (D₀.matrix (fun _ => 1) 1 1)
    hcop (hbad.trans hr) hu hu₀ (hbad.trans hd)
  rw [ShortDraftCusp.A4BadPhase_as_fixed_residue, ShortDraftCusp.A4BadPhase_as_fixed_residue]
  congr 1
  exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr he)

end
end SevenEighths.InverseReflectedPhase

end OAI
