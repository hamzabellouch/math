import OAI.Geometry.Immersion.ClosedSurface.GoodPhases

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes ClosedSurfaceR4.PhaseMean Set

lemma good_smul {n : ℕ} {B : Fin 3 → RVec n} {ξ : Base} {w : ℝ}
    (hw : w ≠ 0) (h : Good B ξ) : Good B (w • ξ) := by
  constructor
  · exact smul_ne_zero hw h.1
  · have he : (-(w • ξ).2, (w • ξ).1) = w • (-ξ.2, ξ.1) := by ext <;> simp
    rw [he, secondQuadratic_smul]
    exact smul_ne_zero (pow_ne_zero 2 hw) h.2



theorem uniform_good_perturbation {X : Type*} [TopologicalSpace X] {n : ℕ}
    {K : Set X} (hK : IsCompact K) {B : X → Fin 3 → RVec n} {ξ υ : X → Base}
    (hB : Continuous B) (hξ : Continuous ξ) (hυ : Continuous υ)
    (hgood : ∀ p ∈ K, Good (B p) (ξ p)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε → ∀ p ∈ K, Good (B p) (ξ p + t • υ p) := by
  let U : Set (X × ℝ) := {z | Good (B z.1) (ξ z.1 + z.2 • υ z.1)}
  have hU : IsOpen U := isOpen_good (hB.comp continuous_fst)
    ((hξ.comp continuous_fst).add (continuous_snd.smul (hυ.comp continuous_fst)))
  have hKU : K ×ˢ ({0} : Set ℝ) ⊆ U := by
    rintro ⟨p, t⟩ ⟨hp, ht⟩
    simp only [mem_singleton_iff] at ht
    subst t
    simpa [U] using hgood p hp
  obtain ⟨V, W, hV, hW, hKV, h0W, hprod⟩ :=
    generalized_tube_lemma hK isCompact_singleton hU hKU
  obtain ⟨ε, hε, heW⟩ := Metric.isOpen_iff.mp hW 0 (h0W (by simp))
  refine ⟨ε, hε, fun t ht p hp => ?_⟩
  change (p, t) ∈ U
  apply hprod ⟨hKV hp, heW ?_⟩
  simpa [Metric.mem_ball, Real.dist_eq] using ht




theorem exists_dominant_weight {ι : Type*} [Fintype ι]
    {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, CompactSpace (X i)]
    {n : ℕ} (B : ∀ i, X i → Fin 3 → RVec n) (ξ υ : ∀ i, X i → Base)
    (hB : ∀ i, Continuous (B i)) (hξ : ∀ i, Continuous (ξ i))
    (hυ : ∀ i, Continuous (υ i)) (hgood : ∀ i p, Good (B i p) (ξ i p))
    (c : ι → ℝ) :
    ∃ w : ℝ, 0 < w ∧ ∀ i p,
      Good (B i p) (w • ξ i p + c i • υ i p) ∧
      Good (B i p) (w • ξ i p - c i • υ i p) := by
  classical
  have hsmall : ∀ i, ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε → ∀ p,
      Good (B i p) (ξ i p + t • υ i p) := by
    intro i
    obtain ⟨ε, hε, ht⟩ := uniform_good_perturbation (K := univ) isCompact_univ
      (hB i) (hξ i) (hυ i) (fun p _ => hgood i p)
    exact ⟨ε, hε, fun t htp p => ht t htp p (mem_univ p)⟩
  choose ε hε hsmall using hsmall
  let w := 1 + ∑ i, |c i| / ε i
  have hw : 0 < w := by
    dsimp [w]
    exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun i _ => div_nonneg (abs_nonneg _) (hε i).le)
  have hc : ∀ i, |c i / w| < ε i := by
    intro i
    have hsum := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) =>
      div_nonneg (abs_nonneg (c j)) (hε j).le) (Finset.mem_univ i)
    have hb : |c i| / ε i < w := by dsimp [w]; linarith
    rw [abs_div, abs_of_pos hw, div_lt_iff₀ hw]
    have ht := (div_lt_iff₀ (hε i)).mp hb
    nlinarith
  refine ⟨w, hw, fun i p => ⟨?_, ?_⟩⟩
  · have hg := good_smul hw.ne' (hsmall i (c i / w) (hc i) p)
    convert hg using 1
    rw [smul_add, smul_smul, mul_div_cancel₀ _ hw.ne']
  · have hg := good_smul hw.ne' (hsmall i (-(c i / w)) (by simpa using hc i) p)
    convert hg using 1
    rw [smul_add, smul_smul]
    simp only [mul_neg, mul_div_cancel₀ _ hw.ne', neg_smul, sub_eq_add_neg]

end ClosedSurfaceR4.PhaseGeometry

namespace ClosedSurfaceR4.PhaseGeometry
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes ClosedSurfaceR4.PhaseMean Set




theorem finite_good_weights {X : ℕ → ℕ → Type*}
    [∀ i j, TopologicalSpace (X i j)] [∀ i j, CompactSpace (X i j)] {n : ℕ}
    (B : ∀ i j, X i j → Fin 3 → RVec n) (L R : ∀ i j, X i j → Base)
    (hB : ∀ i j, Continuous (B i j)) (hL : ∀ i j, Continuous (L i j))
    (hR : ∀ i j, Continuous (R i j))
    (hgood : ∀ i j, i < j → ∀ p, Good (B i j p) (R i j p)) (N : ℕ) :
    ∃ w : ℕ → ℝ, (∀ i, i < N → 0 < w i) ∧
      ∀ i j, i < j → j < N → ∀ p,
        Good (B i j p) (w i • L i j p + w j • R i j p) ∧
        Good (B i j p) (w i • L i j p - w j • R i j p) := by
  classical
  induction N with
  | zero =>
      refine ⟨fun _ => 1, ?_, ?_⟩
      · intro i hi; omega
      · intro i j hij hj; omega
  | succ N ih =>
      obtain ⟨w, hwpos, hwgood⟩ := ih
      obtain ⟨lam, hlam, hlamgood⟩ := exists_dominant_weight
        (ι := Fin N) (X := fun i => X i N)
        (fun i => B i N) (fun i => R i N) (fun i => L i N)
        (fun i => hB i N) (fun i => hR i N) (fun i => hL i N)
        (fun i p => hgood i N i.isLt p) (fun i => w i)
      let w' : ℕ → ℝ := fun i => if i = N then lam else w i
      refine ⟨w', ?_, ?_⟩
      · intro i hi
        by_cases hiN : i = N
        · simpa [w', hiN] using hlam
        · have hiN' : i < N := by omega
          simpa [w', hiN] using hwpos i hiN'
      · intro i j hij hj p
        by_cases hjN : j = N
        · subst j
          have hiN : i ≠ N := Nat.ne_of_lt hij
          have hp := hlamgood ⟨i, hij⟩ p
          constructor
          · simpa [w', hiN, add_comm] using hp.1
          · have hn := good_neg hp.2
            simpa [w', hiN, neg_sub] using hn
        · have hjN' : j < N := by omega
          have hiN : i ≠ N := Nat.ne_of_lt (hij.trans hjN')
          simpa [w', hiN, hjN] using hwgood i j hij hjN' p

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
