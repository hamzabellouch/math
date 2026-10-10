import Mathlib
import OAI.Analysis.SymmetricDomains.GenericRealParameterPolynomial
import OAI.Analysis.SymmetricDomains.BoundaryFiberClosureContinuity

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter Topology Metric MeasureTheory Classical

theorem semialgebraic_boundary_fiber_closure {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] (A : (Fin n → ℝ) → Set E)
    (B : Set (Fin n → ℝ)) (hB : IsOpen B)
    (hgraph : PolynomialSignSet id
      {x : Option (Fin n) → ℝ |
        (fun i => x (some i)) ∈ B ∧
          x none = inwardDistance A (fun i => x (some i))})
    (hb : ∀ s ∈ B, (s,(0 : E)) ∈ closure {p : (Fin n → ℝ) × E | p.2 ∈ A p.1}) :
    ∃ B' : Set (Fin n → ℝ), IsOpen B' ∧ B' ⊆ B ∧ volume (B \ B') = 0 ∧
      ∀ s ∈ B', (0 : E) ∈ closure (A s) := by
  obtain ⟨D,hD,hreg⟩ := semialgebraic_function_analytic_off_polynomial
    B (inwardDistance A) hgraph
  let B' := B ∩ {s | MvPolynomial.eval s D ≠ 0}
  have hopen : IsOpen B' := hB.inter
    ((MvPolynomial.continuous_eval D).isOpen_preimage _ isOpen_ne)
  have hsub : B' ⊆ B := inter_subset_left
  have hnull : volume {s : Fin n → ℝ | MvPolynomial.eval s D = 0} = 0 := by
    have hmap := (MvPolynomial.map_injective (σ := Fin n) Complex.ofRealHom
      Complex.ofReal_injective).ne hD
    have hn := complex_polynomial_real_zero_null
      (MvPolynomial.map Complex.ofRealHom D) (by simpa only [map_zero] using hmap)
    have he : {s : Fin n → ℝ |
        MvPolynomial.eval (fun i => (s i : ℂ)) (MvPolynomial.map Complex.ofRealHom D) = 0} =
        {s : Fin n → ℝ | MvPolynomial.eval s D = 0} := by
      ext s
      change MvPolynomial.eval (realParameter s) (MvPolynomial.map Complex.ofRealHom D) = 0 ↔ _
      rw [complexify_mv_eval,Complex.ofReal_eq_zero]
      rfl
    rwa [he] at hn
  refine ⟨B',hopen,hsub,?_,?_⟩
  · apply measure_mono_null _ hnull
    intro s hs
    by_contra hn
    exact hs.2 ⟨hs.1,hn⟩
  · intro s hs
    exact boundary_fiber_closure_at_continuity A s
      (hreg s hs.1 hs.2).continuousAt (hb s hs.1)

end

open Set Complex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {k : ℕ}

def quadraticDomain (H : E → Fin k → ℝ) (C : Set (Fin k → ℝ)) :
    Set (E × (Fin k → ℂ)) := {p | (fun i => (p.2 i).im-H p.1 i) ∈ C}

def quadraticDomainCoordinates (H : E → Fin k → ℝ) (hH : Continuous H) :
    (E × (Fin k → ℂ)) ≃ₜ (E × ((Fin k → ℝ) × (Fin k → ℝ))) where
  toFun p := (p.1,(fun i => (p.2 i).re,fun i => (p.2 i).im-H p.1 i))
  invFun p := (p.1,fun i => ((p.2.1 i : ℂ)+I*((p.2.2 i+H p.1 i : ℝ) : ℂ)))
  left_inv p := by
    apply Prod.ext
    · rfl
    funext i
    apply Complex.ext <;> simp
  right_inv p := by
    apply Prod.ext
    · rfl
    apply Prod.ext <;> funext i <;> simp
  continuous_toFun := by
    apply Continuous.prodMk continuous_fst
    apply Continuous.prodMk
    · apply continuous_pi
      intro i
      exact Complex.continuous_re.comp ((continuous_apply i).comp continuous_snd)
    · apply continuous_pi
      intro i
      exact (Complex.continuous_im.comp ((continuous_apply i).comp continuous_snd)).sub
        (((continuous_apply i).comp hH).comp continuous_fst)
  continuous_invFun := by
    apply Continuous.prodMk continuous_fst
    apply continuous_pi
    intro i
    exact (Complex.continuous_ofReal.comp
      ((continuous_apply i).comp (continuous_fst.comp continuous_snd))).add
      ((Complex.continuous_ofReal.comp
        (((continuous_apply i).comp (continuous_snd.comp continuous_snd)).add
          (((continuous_apply i).comp hH).comp continuous_fst))).const_mul I)

omit [NormedSpace ℂ E] in
lemma quadraticDomain_eq_preimage (H : E → Fin k → ℝ) (hH : Continuous H)
    (C : Set (Fin k → ℝ)) :
    quadraticDomain H C = (quadraticDomainCoordinates H hH) ⁻¹' (univ ×ˢ (univ ×ˢ C)) := by
  ext p
  simp only [quadraticDomain,mem_ofPred_eq,mem_preimage,mem_prod,mem_univ,true_and]
  rfl

omit [NormedSpace ℂ E] in
theorem quadraticDomain_isOpen (H : E → Fin k → ℝ) (hH : Continuous H)
    (C : Set (Fin k → ℝ)) (hC : IsOpen C) : IsOpen (quadraticDomain H C) := by
  rw [quadraticDomain_eq_preimage H hH]
  exact (isOpen_univ.prod (isOpen_univ.prod hC)).preimage
    (quadraticDomainCoordinates H hH).continuous

theorem quadraticDomain_isConnected (H : E → Fin k → ℝ) (hH : Continuous H)
    (C : Set (Fin k → ℝ)) (hC : IsConnected C) : IsConnected (quadraticDomain H C) := by
  rw [quadraticDomain_eq_preimage H hH]
  exact (quadraticDomainCoordinates H hH).isConnected_preimage.mpr
    (isConnected_univ.prod (isConnected_univ.prod hC))

omit [NormedSpace ℂ E] in
lemma quadraticDomain_axis (H : E → Fin k → ℝ) (hH0 : H 0 = 0)
    {C : Set (Fin k → ℝ)} {a : Fin k → ℝ} (ha : a ∈ C) :
    ((0 : E),fun i => I*(a i : ℂ)) ∈ quadraticDomain H C := by
  simpa [quadraticDomain,hH0] using ha

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
lemma quadraticDomain_translation (H : E → Fin k → ℝ) (C : Set (Fin k → ℝ))
    (p : E × (Fin k → ℂ)) (a : Fin k → ℝ) :
    (p.1,fun i => p.2 i+(a i : ℂ)) ∈ quadraticDomain H C ↔ p ∈ quadraticDomain H C := by
  simp [quadraticDomain]

lemma quadraticDomain_unit_rotation (H : E → Fin k → ℝ) (C : Set (Fin k → ℝ))
    (c : ℂ) (hHc : ∀ z, H (c • z) = H z) (p : E × (Fin k → ℂ)) :
    (c • p.1,p.2) ∈ quadraticDomain H C ↔ p ∈ quadraticDomain H C := by
  simp [quadraticDomain,hHc]

lemma quadraticDomain_positive_dilation [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    (H : E → Fin k → ℝ) (C : Set (Fin k → ℝ)) (r : ℝ)
    (hH : ∀ z, H (Real.sqrt r • z) = r • H z)
    (hC : ∀ v, r • v ∈ C ↔ v ∈ C) (p : E × (Fin k → ℂ)) :
    (Real.sqrt r • p.1,r • p.2) ∈ quadraticDomain H C ↔ p ∈ quadraticDomain H C := by
  have he : (fun i => ((r • p.2) i).im-H (Real.sqrt r • p.1) i) =
      r • (fun i => (p.2 i).im-H p.1 i) := by
    funext i
    simp only [hH,Pi.smul_apply,Complex.real_smul,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,smul_eq_mul]
    ring
  change (fun i => ((r • p.2) i).im-H (Real.sqrt r • p.1) i) ∈ C ↔ _
  rw [he,hC]
  rfl

theorem quadraticDomain_connectedComponent (H : E → Fin k → ℝ)
    (hH : Continuous H) (C : Set (Fin k → ℝ)) (p : E × (Fin k → ℂ)) :
    connectedComponentIn (quadraticDomain H C) p =
      quadraticDomain H (connectedComponentIn C (fun i => (p.2 i).im-H p.1 i)) := by
  let q : E × (Fin k → ℂ) → Fin k → ℝ := fun x i => (x.2 i).im-H x.1 i
  have hq : Continuous q := by
    apply continuous_pi
    intro i
    exact (Complex.continuous_im.comp ((continuous_apply i).comp continuous_snd)).sub
      (((continuous_apply i).comp hH).comp continuous_fst)
  change connectedComponentIn (quadraticDomain H C) p =
    quadraticDomain H (connectedComponentIn C (q p))
  by_cases hp : p ∈ quadraticDomain H C
  · have hpc : q p ∈ C := hp
    apply Subset.antisymm
    · intro x hx
      have hpre : IsPreconnected (q '' connectedComponentIn (quadraticDomain H C) p) :=
        isPreconnected_connectedComponentIn.image q hq.continuousOn
      have hmem : q p ∈ q '' connectedComponentIn (quadraticDomain H C) p :=
        ⟨p,mem_connectedComponentIn hp,rfl⟩
      have hsub : q '' connectedComponentIn (quadraticDomain H C) p ⊆ C := by
        rintro _ ⟨y,hy,rfl⟩
        exact connectedComponentIn_subset (quadraticDomain H C) p hy
      exact hpre.subset_connectedComponentIn hmem hsub ⟨x,hx,rfl⟩
    · have hpre := (quadraticDomain_isConnected H hH (connectedComponentIn C (q p))
        (isConnected_connectedComponentIn_iff.mpr hpc)).isPreconnected
      have hmem : p ∈ quadraticDomain H (connectedComponentIn C (q p)) :=
        mem_connectedComponentIn hpc
      have hsub : quadraticDomain H (connectedComponentIn C (q p)) ⊆ quadraticDomain H C := by
        intro x hx
        exact connectedComponentIn_subset C (q p) hx
      exact hpre.subset_connectedComponentIn hmem hsub
  · have hpc : q p ∉ C := hp
    rw [connectedComponentIn_eq_empty hp,connectedComponentIn_eq_empty hpc]
    simp [quadraticDomain]

end Release061

end

end OAI
