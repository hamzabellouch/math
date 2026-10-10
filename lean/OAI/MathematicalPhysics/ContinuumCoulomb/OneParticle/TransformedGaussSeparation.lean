import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.TransformedGauss

namespace OAI

/-! Distinctness of the numerical transported nodes. The input labels use
the same integer cells and eight sign choices as the exact Gauss grid. -/

noncomputable section
open scoped NNReal
namespace ContinuumCoulomb.TransformedGauss
open CappedKernelProgram (Triple position)
open EulerRegisters (Registers)
open RationalGaussNodes (Signs)

private theorem sign_injective {a b : Bool}
    (h : (if a then (1:Fin 2) else 0) = (if b then (1:Fin 2) else 0)) : a = b := by
  cases a <;> cases b <;> simp_all

theorem index_injective : Function.Injective (fun x : Registers×Signs =>
    RationalGaussNodes.index x.1 x.2) := by
  rintro ⟨k,b⟩ ⟨l,c⟩ h
  have h0 : k.1 = l.1 := by
    simpa [RationalGaussNodes.index] using congrArg (fun x : GaussLatticeIndex => x.1 0) h
  have h1 : k.2.1 = l.2.1 := by
    simpa [RationalGaussNodes.index] using congrArg (fun x : GaussLatticeIndex => x.1 1) h
  have h2 : k.2.2 = l.2.2 := by
    simpa [RationalGaussNodes.index] using congrArg (fun x : GaussLatticeIndex => x.1 2) h
  have hb0 : b.1 = c.1 := sign_injective (by
    simpa [RationalGaussNodes.index] using congrArg (fun x : GaussLatticeIndex => x.2 0) h)
  have hb1 : b.2.1 = c.2.1 := sign_injective (by
    simpa [RationalGaussNodes.index] using congrArg (fun x : GaussLatticeIndex => x.2 1) h)
  have hb2 : b.2.2 = c.2.2 := sign_injective (by
    simpa [RationalGaussNodes.index] using congrArg (fun x : GaussLatticeIndex => x.2 2) h)
  exact Prod.ext (Prod.ext h0 (Prod.ext h1 h2)) (Prod.ext hb0 (Prod.ext hb1 hb2))

theorem value_injective {I : Type*} (labels : I → Registers×Signs)
    (hlabels : Function.Injective labels) (rho U C K P : ℕ) {N : ℕ} (hN : 0 < N)
    (scale S : ℚ) (sites : List (ℚ×ℚ)) (G : Position → Position)
    {J : ℝ≥0} (hG : AntilipschitzWith J G)
    (herror : ∀ i,
      ‖position (value rho U C K P N scale S sites (labels i).1 (labels i).2)-
        G (gaussLatticePoint (N:ℝ)⁻¹ (RationalGaussNodes.index (labels i).1 (labels i).2))‖ ≤
          ((P:ℝ)+1)⁻¹)
    (hprecision : 2*(J:ℝ)*((P:ℝ)+1)⁻¹ < (N:ℝ)⁻¹/3) :
    Function.Injective (fun i => value rho U C K P N scale S sites (labels i).1 (labels i).2) := by
  intro i j hij
  by_contra hne
  have hindices : RationalGaussNodes.index (labels i).1 (labels i).2 ≠
      RationalGaussNodes.index (labels j).1 (labels j).2 := by
    intro he
    exact hne (hlabels (index_injective he))
  have hbase := gaussLatticePoint_separation
    (show 0 < (N:ℝ)⁻¹ by positivity) _ _ hindices
  have htrans := hG.le_mul_dist
    (gaussLatticePoint (N:ℝ)⁻¹ (RationalGaussNodes.index (labels i).1 (labels i).2))
    (gaussLatticePoint (N:ℝ)⁻¹ (RationalGaussNodes.index (labels j).1 (labels j).2))
  simp only [dist_eq_norm] at htrans
  have hi := herror i
  have hj := herror j
  have he := congrArg position hij
  rw [he] at hi
  have ht : ‖G (gaussLatticePoint (N:ℝ)⁻¹ (RationalGaussNodes.index (labels i).1 (labels i).2))-
      G (gaussLatticePoint (N:ℝ)⁻¹ (RationalGaussNodes.index (labels j).1 (labels j).2))‖ ≤
        2*((P:ℝ)+1)⁻¹ := by
    calc
      _ ≤ ‖G (gaussLatticePoint (N:ℝ)⁻¹ (RationalGaussNodes.index (labels i).1 (labels i).2))-
          position (value rho U C K P N scale S sites (labels i).1 (labels i).2)‖+
          ‖position (value rho U C K P N scale S sites (labels i).1 (labels i).2)-
          G (gaussLatticePoint (N:ℝ)⁻¹ (RationalGaussNodes.index (labels j).1 (labels j).2))‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := by rw [norm_sub_rev _ (position _),he]; linarith
  have hmul := mul_le_mul_of_nonneg_left ht J.coe_nonneg
  nlinarith

end ContinuumCoulomb.TransformedGauss

end

end OAI
