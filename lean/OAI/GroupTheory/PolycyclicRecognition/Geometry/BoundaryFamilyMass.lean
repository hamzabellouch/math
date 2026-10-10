import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundaryImageMass

namespace OAI

/-! # Uniform masses and equal-set traces for a compact-shadow family -/

noncomputable section
namespace PolycyclicRecognition

open Set MeasureTheory TopologicalSpace
open scoped ENNReal

/-- The compact shadows provide a single source window with uniform mass
and trace bounds. A compact set with interior in the source can be retained
inside this window for the subsequent averaging argument. -/
theorem boundary_family_mass_and_trace_of_compact_shadows
    {P G S T : Type*} [Group G] [MetricSpace G] [IsTopologicalGroup G]
    [IsIsometricSMul G G] [ProperSpace G]
    [One S] [TopologicalSpace S]
    [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T]
    [MeasurableSpace T] [BorelSpace T]
    (actS : G →* Equiv.Perm S) (actT : G →* Equiv.Perm T)
    (hcontS : Continuous (fun g => actS g 1))
    (hcontT : Continuous (fun g => actT g 1))
    (B : P → S → T) (C : P → T → S) (f g : P → G → G)
    {Lf Lg ef eg E : ℝ} (hLf : 0 ≤ Lf) (hLg : 0 ≤ Lg)
    (hf : ∀ p x y, dist (f p x) (f p y) ≤ Lf * dist x y + ef)
    (hg : ∀ p x y, dist (g p x) (g p y) ≤ Lg * dist x y + eg)
    (hinv : ∀ p x, dist (g p (f p x)) x ≤ E)
    (hBC : ∀ p, Function.RightInverse (C p) (B p))
    (σS : S → G) (hσS : Continuous σS) (hsectionS : ∀ q, actS (σS q) 1 = q)
    (σT : T → G) (hσT : Continuous σT) (hsectionT : ∀ q, actT (σT q) 1 = q)
    (KS : Set S) (KT : Set T) (hKS : IsCompact KS) (hKT : IsCompact KT)
    (hB : ∀ p x, ∃ q ∈ KT, B p (actS x 1) = actT (f p x) q)
    (hC : ∀ p x, ∃ q ∈ KS, C p (actT x 1) = actS (g p x) q)
    (μ : Measure T) [μ.IsHaarMeasure] (height : G → ℝ)
    (hvolume : ∀ x V, μ (actT x '' V) = ENNReal.ofReal (Real.exp (height x)) * μ V)
    (U₀ : Set S) (hU₀ : IsCompact U₀) :
    ∃ (U : Set S) (K D : ℝ), IsCompact U ∧ U₀ ⊆ U ∧ 0 < K ∧ 0 ≤ D ∧
      (∀ p x, ENNReal.ofReal (Real.exp (height (f p x))) ≤
          ENNReal.ofReal K * μ (B p '' (actS x '' U)) ∧
        μ (B p '' (actS x '' U)) ≤
          ENNReal.ofReal K * ENNReal.ofReal (Real.exp (height (f p x)))) ∧
      ∀ p x y, actS x '' U = actS y '' U → |height (f p x) - height (f p y)| ≤ D := by
  classical
  let Vminus : PositiveCompacts T := Classical.choice inferInstance
  have hVminus0 : μ (Vminus : Set T) ≠ 0 :=
    (Measure.measure_pos_of_nonempty_interior μ Vminus.interior_nonempty).ne'
  have hVminusfin : μ (Vminus : Set T) ≠ ⊤ := Vminus.isCompact.measure_ne_top
  let KSG := σS '' KS
  let KTG := σT '' KT
  have hB' : ∀ p x, ∃ v ∈ KTG, B p (actS x 1) = actT (f p x) (actT v 1) := by
    intro p x
    obtain ⟨q, hq, he⟩ := hB p x
    exact ⟨σT q, ⟨q, hq, rfl⟩, by simpa only [hsectionT] using he⟩
  have hC' : ∀ p x, ∃ v ∈ KSG, C p (actT x 1) = actS (g p x) (actS v 1) := by
    intro p x
    obtain ⟨q, hq, he⟩ := hC p x
    exact ⟨σS q, ⟨q, hq, rfl⟩, by simpa only [hsectionS] using he⟩
  obtain ⟨U, Vplus, hU, hVplus, hU₀U, hsandwich⟩ := boundary_image_compact_sandwich
    actS actT hcontS hcontT B C f g hLf hLg hf hg hinv hBC
    σS hσS hsectionS σT hσT hsectionT KSG KTG (hKS.image hσS) (hKT.image hσT)
    hB' hC' U₀ hU₀ Vminus Vminus.isCompact
  obtain ⟨K, hK, hmass⟩ := boundary_image_mass_bounds actS actT B f μ height hvolume
    U Vminus Vplus hVminus0 hVminusfin hVplus.measure_ne_top hsandwich
  obtain ⟨D, hD, htrace⟩ := boundary_trace_bound_of_sandwich actS actT B f μ height hvolume
    U Vminus Vplus hVminus0 hVminusfin hVplus.measure_ne_top hsandwich
  exact ⟨U, K, D, hU, hU₀U, hK, hD, hmass, htrace⟩

end PolycyclicRecognition

end

end OAI
