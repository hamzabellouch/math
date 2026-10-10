import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.SparseClusters
import OAI.Probability.LatticeSurface.Convexity.ProductData
import OAI.Probability.LatticeSurface.Convexity.ProductGraph
import OAI.Probability.LatticeSurface.Convexity.ProductVolume
import OAI.Probability.LatticeSurface.Dynamics.ClusterShift
import OAI.Probability.LatticeSurface.Dynamics.JacobianIdentity
import OAI.Probability.LatticeSurface.Dynamics.LogDet
import OAI.Probability.LatticeSurface.Dynamics.MatrixJacobi
import OAI.Probability.LatticeSurface.Dynamics.ShiftAnalysis
import OAI.Probability.LatticeSurface.Dynamics.ShiftAssembly
import OAI.Probability.LatticeSurface.Dynamics.ShiftAsymptotics
import OAI.Probability.LatticeSurface.Dynamics.ShiftData

namespace OAI

universe u v

open Set MeasureTheory

open Filter

namespace FeasibleShift

open Filter

theorem feasible_shifts_product {ι : Type*} [Fintype ι]
    (D Db B : ℕ) (ρ : ENNReal) (s₀ s₁ s₂ sstar L M N p : ℝ)
    (hB : 0 < B) (hρ : ρ ≤ 1) (hsparse : (Db : ENNReal)^2 * ρ ≤ 1/2)
    (hs₀ : 0 < s₀) (hs : s₀ < s₁) (hss : s₁ < s₂) (hstar : s₂ < sstar)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hN : 0 ≤ N) (hp : 0 < p) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      Tendsto (fun n : ℕ => (L / n) * (n : ℝ)^(1/8 : ℝ)) atTop (nhds 0) ∧
      ∀ (n : ℕ), n₀ ≤ n → ∀ (V : ι → Type u) [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
        (W : ι → Type v) [∀ i, Fintype (W i)] [∀ i, DecidableEq (W i)]
        (S : ∀ i, ShiftData (V := V i) (W i) n D Db B ρ sstar L M N)
        (E : Set (∀ i, FreeSites (S i).pins → ℝ)),
        MeasurableSet E → p ≤ (MeasureTheory.Measure.pi (fun i => (S i).law)).real E →
        ∃ E' : Set (∀ i, FreeSites (S i).pins → ℝ), MeasurableSet E' ∧ E' ⊆ E ∧
          p/2 ≤ (MeasureTheory.Measure.pi (fun i => (S i).law)).real E' ∧
          Set.InjOn (fun h i => (S i).map s₀ s₁ (h i)) E' ∧
          (fun h i => (S i).map s₀ s₁ (h i)) '' E' ⊆ Set.pi Set.univ (fun i => (S i).polytope) ∧
          MeasurableSet ((fun h i => (S i).map s₀ s₁ (h i)) '' E') ∧
          (∀ h ∈ E', ‖(fun i => (S i).map s₀ s₁ (h i) - h i -
            (fun x : FreeSites (S i).pins => (S i).prescribed x))‖ ≤
            (L / n) * (n : ℝ)^(1/8 : ℝ)) ∧
          c ≤ (MeasureTheory.Measure.pi (fun i => (S i).law)).real
            ((fun h i => (S i).map s₀ s₁ (h i)) '' E') := by
  classical
  obtain ⟨c,hc,n₀,ht,hn₀⟩ := feasible_shifts D Db B ρ s₀ s₁ s₂ sstar L M
    (N * Fintype.card ι) p hB hρ hsparse hs₀ hs hss hstar hL hM (by positivity) hp
  refine ⟨c,hc,n₀,ht,?_⟩
  intro n hn V iV dV W iW dW S E hE hEp
  let U := DisjointUnion.combine S
  let e : (FreeSites U.pins → ℝ) ≃ᵐ (∀ i, FreeSites (S i).pins → ℝ) :=
    DisjointUnion.heightEquiv (fun i => (S i).pins)
  let μ := MeasureTheory.Measure.pi (fun i => (S i).law)
  have he : MeasureTheory.MeasurePreserving e U.law μ := DisjointUnion.combine_law S
  have him (A : Set (FreeSites U.pins → ℝ)) : μ (e '' A) = U.law A := by
    rw [← DisjointUnion.equiv_measure_preimage e he,
      Set.preimage_image_eq A e.injective]
  have himr (A : Set (FreeSites U.pins → ℝ)) : μ.real (e '' A) = U.law.real A :=
    congrArg ENNReal.toReal (him A)
  have hEp' : p ≤ U.law.real (e ⁻¹' E) := by
    simpa only [MeasureTheory.measureReal_def, DisjointUnion.equiv_measure_preimage e he] using hEp
  obtain ⟨F,hFm,hFE,hFp,hFj,hFimage,hFim,hFerr,hFc⟩ :=
    hn₀ n hn (Sigma V) (Sigma W) U (e ⁻¹' E) (hE.preimage e.measurable) hEp'
  let T : (∀ i, FreeSites (S i).pins → ℝ) → (∀ i, FreeSites (S i).pins → ℝ) :=
    fun h i => (S i).map s₀ s₁ (h i)
  have hmap (h : FreeSites U.pins → ℝ) : e (U.map s₀ s₁ h) = T (e h) :=
    DisjointUnion.combine_map S s₀ s₁ h
  have hTi : T '' (e '' F) = e '' (U.map s₀ s₁ '' F) := by
    simp only [Set.image_image]
    congr 1
    exact funext (fun h => (hmap h).symm)
  refine ⟨e '' F, e.measurableEmbedding.measurableSet_image.mpr hFm,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨h,hh,rfl⟩
    exact hFE hh
  · change p/2 ≤ μ.real (e '' F)
    rw [himr]
    exact hFp
  · change Set.InjOn T (e '' F)
    rintro _ ⟨h,hh,rfl⟩ _ ⟨k,hk,rfl⟩ hhk
    apply congrArg e
    apply hFj hh hk
    exact e.injective ((hmap h).trans (hhk.trans (hmap k).symm))
  · change T '' (e '' F) ⊆ Set.pi Set.univ (fun i => (S i).polytope)
    rw [hTi]
    rintro _ ⟨h,hh,rfl⟩
    have hhp := hFimage hh
    change h ∈ e ⁻¹' Set.pi Set.univ (fun i => (S i).polytope)
    have hp' : h ∈ DisjointUnion.combinedPolytope S := hhp
    rw [DisjointUnion.combinedPolytope_eq S] at hp'
    exact hp'
  · change MeasurableSet (T '' (e '' F))
    rw [hTi]
    exact e.measurableEmbedding.measurableSet_image.mpr hFim
  · rintro _ ⟨h,hh,rfl⟩
    have hR : 0 ≤ (L / n) * (n:ℝ)^(1/8:ℝ) := by positivity
    apply (pi_norm_le_iff_of_nonneg hR).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg hR).mpr
    intro x
    let q : FreeSites U.pins := ⟨⟨i,x⟩, by simpa [U, DisjointUnion.combine] using x.2⟩
    have hb := (norm_le_pi_norm (U.map s₀ s₁ h - h - fun y : FreeSites U.pins => U.prescribed y) q).trans
      (hFerr h hh)
    have hm := congrFun (congrFun (hmap h) i) x
    change U.map s₀ s₁ h q = (S i).map s₀ s₁ (e h i) x at hm
    change ‖(S i).map s₀ s₁ (e h i) x - h q - (S i).prescribed x‖ ≤ _
    rw [← hm]
    exact hb
  · change c ≤ μ.real (T '' (e '' F))
    rw [hTi, himr]
    exact hFc

end FeasibleShift

end OAI
