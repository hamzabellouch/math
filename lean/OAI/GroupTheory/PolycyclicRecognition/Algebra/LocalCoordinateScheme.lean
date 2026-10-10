import OAI.GroupTheory.PolycyclicRecognition.Algebra.LocalGeneratorOrbit
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CoordinateSchemeSubmersion
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialCoordinateTopology
import OAI.GroupTheory.PolycyclicRecognition.Algebra.AdmissibleConjugateScheme

namespace OAI

/-! # A full-rank coordinate scheme with admissible conjugating paths -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter Module
open scoped Topology

variable {V I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype I]

theorem coordinateScheme_map_nhds
    {c : ℕ} (a : DynkinCoefficients c 2) (B : V →L[ℝ] V →L[ℝ] V)
    (hB : IsLieBracket B) (hg : PolynomialGroupLaws (dynkinProduct a B))
    (hc : ExponentialConjugationLaw (dynkinProduct a B) B)
    (X : I → V) (b : Basis (Fin (finrank ℝ V)) ℝ V)
    (w : Fin (finrank ℝ V) → List (I × ℝ)) (i : Fin (finrank ℝ V) → I)
    (hb : ∀ k, bilinearAdjointWord B X (w k) (X (i k)) = b k) :
    map (polynomialEndpointScheme a w i (B, X)) (𝓝 0) = 𝓝 0 := by
  let Exp := PolynomialCoordinateGroup.exp (dynkinProduct a B) hg
  have he (t) : Exp (polynomialEndpointScheme a w i (B, X) t) =
      basisExponentialProduct Exp b t := by
    apply polynomialEndpointScheme_basisProduct a B hB hg X b w i
    intro k s
    rw [← hb k, ← map_smul]
    exact exp_bilinearAdjointWord _ hg B hc X (w k) (s • X (i k))
  have hz : polynomialEndpointScheme a w i (B, X) 0 = 0 := by
    apply Exp.injective
    rw [he]
    simp [Exp, basisExponentialProduct]
  have haxis (j : Fin (finrank ℝ V)) (s : ℝ) :
      polynomialEndpointScheme a w i (B, X) (Pi.single j s) = s • b j := by
    apply Exp.injective
    rw [he]
    unfold basisExponentialProduct
    rw [list_prod_ofFn_eq_single _ j (by
      intro k hk
      simp [Pi.single_eq_of_ne hk, Exp])]
    simp [Exp]
  let f := polynomialEndpointScheme a w i (B, X)
  have hdiff : ContDiff ℝ 1 f :=
    (contDiff_polynomialEndpointScheme a w i).comp (contDiff_const.prodMk contDiff_id)
  have hcol (j : Fin (finrank ℝ V)) : fderiv ℝ f 0 (Pi.single j 1) = b j := by
    have hd := hdiff.differentiable_one 0 |>.hasFDerivAt
    have h := hd.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_single j (0 : ℝ)) (by simp)
    have heq : (fun s : ℝ => f (Pi.single j s)) = fun s => s • b j := funext (haxis j)
    change HasDerivAt (fun s : ℝ => f (Pi.single j s)) _ 0 at h
    rw [heq] at h
    exact h.unique (by simpa using (hasDerivAt_id (0 : ℝ)).smul_const (b j))
  have hd (t : Fin (finrank ℝ V) → ℝ) : fderiv ℝ f 0 t = b.equivFun.symm t := by
    calc
      _ = fderiv ℝ f 0 (∑ j, t j • Pi.single j (1 : ℝ)) :=
        congrArg _ (pi_eq_sum_univ' t)
      _ = ∑ j, t j • b j := by simp only [map_sum, map_smul, hcol]
      _ = _ := by
        simpa only [LinearEquiv.apply_symm_apply] using b.sum_equivFun (b.equivFun.symm t)
  have hs : (fderiv ℝ f 0).range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro y
    refine ⟨b.equivFun y, ?_⟩
    change fderiv ℝ f 0 (b.equivFun y) = y
    rw [hd, LinearEquiv.symm_apply_apply]
  simpa only [f, hz] using (hdiff.contDiffAt.hasStrictFDerivAt one_ne_zero).map_nhds_eq_of_surj hs

end PolycyclicRecognition

end

end OAI
