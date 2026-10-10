import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousTopCommutator
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousConjugation

namespace OAI

/-! # Physical Cartesian derivatives commute with complex conjugation -/

open MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def homogeneousPhysicalSchwartzStar (f : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  SchwartzMap.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ) f

@[simp] theorem homogeneousPhysicalSchwartzStar_apply (f : 𝓢(E, ℂ)) (x : E) :
    homogeneousPhysicalSchwartzStar f x = star (f x) := rfl

theorem homogeneousConjugation_Schwartz (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (f : 𝓢(E, ℂ)) :
    homogeneousConjugation a k ha ha1 hk (homogeneousSchwartzEmbedding a k ha ha1 hk f) =
      homogeneousSchwartzEmbedding a k ha ha1 hk (homogeneousPhysicalSchwartzStar f) := by
  apply homogeneousPhysicalCLM_injective a k ha ha1 hk
  apply DFunLike.ext
  intro x
  rw [homogeneousConjugation_physical, homogeneousPhysicalCLM_Schwartz,
    homogeneousPhysicalCLM_Schwartz]
  rfl

theorem homogeneousOrderedDerivative_star (N : ℕ) (j : Fin N → Fin 12) (f : 𝓢(E, ℂ)) :
    homogeneousOrderedDerivative N j (homogeneousPhysicalSchwartzStar f) =
      homogeneousPhysicalSchwartzStar (homogeneousOrderedDerivative N j f) := by
  apply SchwartzMap.ext
  intro x
  change (∂^{fun i => (EuclideanSpace.basisFun (Fin 12) ℝ) (j i)}
      (homogeneousPhysicalSchwartzStar f)) x =
    star ((∂^{fun i => (EuclideanSpace.basisFun (Fin 12) ℝ) (j i)} f) x)
  rw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv,
    SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
  have h := Complex.conjCLE.iteratedFDeriv_comp_left (f := (f : E → ℂ)) (x := x) (i := N)
  exact congrArg (fun L => L (fun i => (EuclideanSpace.basisFun (Fin 12) ℝ) (j i))) h

private theorem homogeneousPhysicalSchwartzStar_toLp (f : 𝓢(E, ℂ)) :
    (homogeneousPhysicalSchwartzStar f).toLp 2 volume = star (f.toLp 2 volume) := by
  apply Lp.ext
  filter_upwards [SchwartzMap.coeFn_toLp (homogeneousPhysicalSchwartzStar f) 2 volume,
    SchwartzMap.coeFn_toLp f 2 volume, Lp.coeFn_star (f.toLp 2 volume)] with x hout hf hstar
  rw [hout, hstar, Pi.star_apply, hf, homogeneousPhysicalSchwartzStar_apply]

theorem homogeneousPhysicalDerivative_conjugation (a : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < (N : ℝ)) (j : Fin N → Fin 12)
    (u : HomogeneousY a N) :
    homogeneousPhysicalDerivative a N ha ha1 hk j (homogeneousConjugation a N ha ha1 hk u) =
      star (homogeneousPhysicalDerivative a N ha ha1 hk j u) := by
  have hstar : Continuous (star : Lp ℂ 2 (volume : Measure E) → Lp ℂ 2 volume) := by
    let A := (Complex.conjCLE : ℂ →L[ℝ] ℂ).compLpL 2 (volume : Measure E)
    have he : (star : Lp ℂ 2 (volume : Measure E) → Lp ℂ 2 volume) = A := by
      funext f
      apply Lp.ext
      filter_upwards [Lp.coeFn_star f,
        (Complex.conjCLE : ℂ →L[ℝ] ℂ).coeFn_compLpL f] with x hs ha
      exact hs.trans ha.symm
    rw [he]
    exact A.continuous
  let D := homogeneousPhysicalDerivative a N ha ha1 hk j
  let C := homogeneousConjugation a N ha ha1 hk
  have h := (homogeneousSchwartzEmbedding_dense a N ha ha1 hk).equalizer
    (D.continuous.comp C.continuous) (hstar.comp D.continuous) (by
      funext f
      change homogeneousPhysicalDerivative a N ha ha1 hk j
        (homogeneousConjugation a N ha ha1 hk (homogeneousSchwartzEmbedding a N ha ha1 hk f)) =
          star (homogeneousPhysicalDerivative a N ha ha1 hk j
            (homogeneousSchwartzEmbedding a N ha ha1 hk f))
      rw [homogeneousConjugation_Schwartz, homogeneousPhysicalDerivative_Schwartz,
        homogeneousPhysicalDerivative_Schwartz]
      change (homogeneousOrderedDerivative N j (homogeneousPhysicalSchwartzStar f)).toLp 2 volume =
        star ((homogeneousOrderedDerivative N j f).toLp 2 volume)
      rw [homogeneousOrderedDerivative_star, homogeneousPhysicalSchwartzStar_toLp])
  exact congrFun h u

end DefocusingNLS

end OAI
