import Mathlib
import OAI.Combinatorics.IndependentSets.Geometry.EmbeddingLayerLaw
import OAI.Combinatorics.IndependentSets.PCP.CircleRound
import OAI.Combinatorics.IndependentSets.Reduction.SwapOccurrence
import OAI.Combinatorics.IndependentSets.Expansion.Supported2

namespace OAI

namespace LargeIndependentSets
open scoped Classical BigOperators
open MeasureTheory PhaseTest

structure SamplerParameters where
  n : ℕ
  s : ℕ
  hs : 0 < s
  m : ℕ
  hm : 0 < m
  k : ℕ
  hk : 1 ≤ k
  ρ : ℚ
  hρ : 0 ≤ ρ
  μ : LayerLaw (n+1) s

namespace SamplerParameters
instance (p : SamplerParameters) : NeZero (p.m*2^p.k) :=
  ⟨Nat.ne_of_gt (Nat.mul_pos p.hm (by positivity))⟩

lemma even (p : SamplerParameters) : Even (p.m*2^p.k) := by
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one p.hk))
  refine ⟨p.m*2^k, ?_⟩
  rw [hk,pow_succ]
  ring

noncomputable abbrev law (p : SamplerParameters) (L R : Type) [Fintype L] [Fintype R] :=
  samplerLaw (L:=L) (R:=R) p.μ p.m p.k p.hρ

abbrev Vertices (p : SamplerParameters) (L R C : Type) [Fintype L] [Fintype R] :=
  (p.law L R).Vertices C p.n

noncomputable def location (p : SamplerParameters) {U V L R C : Type} [Fintype L] [Fintype R]
    (lc : LabelCoverData U V L R C) (v : p.Vertices L R C) :=
  sampleLocation lc v.1 p.hs v.2.1

noncomputable def graph (p : SamplerParameters) {U V L R C : Type} [Fintype L] [Fintype R]
    (lc : LabelCoverData U V L R C) : SimpleGraph (p.Vertices L R C) :=
  gridGraph (layeredSystem lc p.n) p.even (p.location lc)

theorem completeness (p : SamplerParameters) {U V L R C : Type} [Fintype L] [Fintype R]
    (lc : LabelCoverData U V L R C) (ℓ : U → L) (ρ : V → R) (h : lc.Satisfied ℓ ρ) :
    (∀ x : GridLocation (LayerAnswer L R (U:=U) (V:=V) (n:=p.n)) (p.m*2^p.k),
      ¬pathDistance (layeredSystem lc p.n).linkLength x (gridAntipode x) ≤ ENNReal.ofReal (1/8)) ∧
    ∃ color : p.Vertices L R C → Fin 3, ∀ u v, (p.graph lc).Adj u v → color u ≠ color v := by
  have hC := layered_completeness lc p.n ℓ ρ h p.even
  exact ⟨hC.1, hC.2 _ (p.location lc)⟩

noncomputable def functions (p : SamplerParameters) {U V L R C : Type} [Fintype L] [Fintype R]
    (lc : LabelCoverData U V L R C) (A : Set (p.Vertices L R C))
    (q : LayerQuestion U V p.n) : (LayerAnswer L R q → Circle) → ℝ :=
  tupleExtension (layeredSystem lc p.n) (p.location lc '' A) q

lemma functions_lipschitz (p : SamplerParameters) {U V L R C : Type} [Fintype L] [Fintype R]
    (lc : LabelCoverData U V L R C) (A : Set (p.Vertices L R C)) (q : LayerQuestion U V p.n) :
    LipschitzWith 64 (p.functions lc A q) :=
  tupleExtension_lipschitz _ _ _

lemma functions_bounded (p : SamplerParameters) {U V L R C : Type} [Fintype L] [Fintype R]
    (lc : LabelCoverData U V L R C) (A : Set (p.Vertices L R C))
    (q : LayerQuestion U V p.n) (x : LayerAnswer L R q → Circle) :
    |p.functions lc A q x| ≤ 1 :=
  abs_le.mpr (tupleExtension_bounds _ _ _ _)

lemma functions_odd (p : SamplerParameters) {U V L R C : Type} [Fintype L] [Fintype R]
    (lc : LabelCoverData U V L R C) (A : Set (p.Vertices L R C))
    (q : LayerQuestion U V p.n) (x : LayerAnswer L R q → Circle) :
    p.functions lc A q (fun z => x z + ((1/2:ℝ):Circle)) = -p.functions lc A q x :=
  tupleExtension_odd _ _ _ _

lemma functions_compatibility (p : SamplerParameters) {U V L R C : Type}
    [Fintype L] [Fintype R] (lc : LabelCoverData U V L R C)
    (hnoclique : ∀ x : GridLocation (LayerAnswer L R (U:=U) (V:=V) (n:=p.n)) (p.m*2^p.k),
      ¬pathDistance (layeredSystem lc p.n).linkLength x (gridAntipode x) ≤ ENNReal.ofReal (1/8))
    (A : Set (p.Vertices L R C)) (hA : (p.graph lc).IsIndepSet A)
    (chain : Fin p.n → C) (i j : Fin (p.n+1)) (hij : i ≤ j)
    (y : MixedTuple L R p.n j.val → Circle) :
    |p.functions lc A (occurrenceQuestion lc chain i) (y ∘ chainComposite lc chain i.val j.val hij) -
      p.functions lc A (occurrenceQuestion lc chain j) y| ≤ 2*64/(p.m*2^p.k:ℕ) := by
  rw [abs_sub_comm]
  have hpath (v : MixedTuple L R p.n j.val → ZMod (p.m*2^p.k)) :
      pathDistance (layeredSystem lc p.n).linkLength
        ⟨occurrenceQuestion lc chain i, v ∘ chainComposite lc chain i.val j.val hij⟩
        ⟨occurrenceQuestion lc chain j, v⟩ = 0 :=
    occurrence_chain_path_zero lc chain i.val j.val hij (Nat.le_of_lt_succ j.isLt) v
  have hh := tupleExtension_compatibility (layeredSystem lc p.n) (D:=p.m*2^p.k)
    p.even hnoclique (p.location lc) A hA
    (q:=occurrenceQuestion lc chain i) (q':=occurrenceQuestion lc chain j)
    (chainComposite lc chain i.val j.val hij) hpath y
  exact hh

theorem density_le_fibers (p : SamplerParameters) {U V L R C : Type}
    [Fintype L] [Fintype R] [Fintype C] (lc : LabelCoverData U V L R C)
    (hnoclique : ∀ x : GridLocation (LayerAnswer L R (U:=U) (V:=V) (n:=p.n)) (p.m*2^p.k),
      ¬pathDistance (layeredSystem lc p.n).linkLength x (gridAntipode x) ≤ ENNReal.ofReal (1/8))
    (A : Finset (p.Vertices L R C)) (hA : (p.graph lc).IsIndepSet (A : Set _)) :
    (A.card : ℝ) / Fintype.card (p.Vertices L R C) ≤
      𝔼 chain : Fin p.n → C, ∑ B, (p.μ.supported.weight B : ℝ) *
        fiberSquare lc chain (p.functions lc A) B.val (supported_nonempty p.hs B) p.m p.ρ p.k := by
  let F := p.functions lc (A : Set _)
  have hon (v : p.Vertices L R C) (hv : v ∈ A) :
      F (p.location lc v).1 (torusGrid (p.location lc v).2) = 1 := by
    rw [show F = tupleExtension (layeredSystem lc p.n) (p.location lc '' (A : Set _)) from rfl]
    rw [tupleExtension_on_grid (layeredSystem lc p.n) p.even hnoclique (p.location lc) A hA]
    exact (grid_independent_bump (layeredSystem lc p.n) p.even hnoclique (p.location lc) A hA).2.2.1 v hv
  have hden := density_le_location_square A (p.location lc)
    (fun x => F x.1 (torusGrid x.2)) hon
  apply hden.trans
  change (𝔼 v : (p.law L R).Vertices C p.n,
    (F (sampleLocation lc v.1 p.hs v.2.1).1
      (torusGrid (sampleLocation lc v.1 p.hs v.2.1).2))^2) ≤ _
  rw [(p.law L R).expect_vertices p.n (fun chain o =>
    (F (sampleLocation lc chain p.hs o).1 (torusGrid (sampleLocation lc chain p.hs o).2))^2)]
  apply le_of_eq
  apply Finset.expect_congr rfl
  intro chain _
  exact sampler_expectation lc chain p.μ p.hρ p.hs p.hm F

end SamplerParameters

theorem finite_source_soundness {δ : ℝ} (hδ : 0 < δ) :
    ∃ p : SamplerParameters, ∃ σ : ℚ, 0 < σ ∧ σ < 1 ∧
    ∀ (U V L R C : Type) [Fintype L] [Fintype R] [Fintype C]
      [Nonempty L] [Nonempty R] [Nonempty C] (lc : LabelCoverData U V L R C),
    lc.Sound (σ:ℝ) →
    (∀ x : GridLocation (LayerAnswer L R (U:=U) (V:=V) (n:=p.n)) (p.m*2^p.k),
      ¬pathDistance (layeredSystem lc p.n).linkLength x (gridAntipode x) ≤ ENNReal.ofReal (1/8)) →
    ∀ A : Finset (p.Vertices L R C), (p.graph lc).IsIndepSet (A : Set _) →
      (A.card : ℝ) / Fintype.card (p.Vertices L R C) < δ := by
  let ε := δ/10
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨β,hβ,K,hK,HT⟩ := actual_aligned_fiber 64 hε
  obtain ⟨m,hm,ρ,hρ,hρ1,hstep,hρK,s,hs,hrare,γ,hγ,hzero,k,hk,hD,hgrid⟩ :=
    finite_parameter_selection (L:=64) hε hβ (by norm_num) K
  obtain ⟨J,hJ,HJ⟩ := canonical_subchain_rules 64 s hγ
  let d := max 1 (J*(m+1)^s)
  have hd : 1 ≤ d := le_max_left _ _
  have hs0 : 0 < s := by omega
  obtain ⟨r,hr,μ,hμ⟩ := distributional_alignment s d (by omega) hd ε hε
  cases r with
  | zero => omega
  | succ n =>
    obtain ⟨σ,hσ,hσ1,hσb⟩ := final_soundness_choice hε (n+1) d
    let p : SamplerParameters := ⟨n,s,hs0,m,hm,k,hk,ρ,hρ.le,μ⟩
    refine ⟨p,σ,hσ,hσ1,?_⟩
    intro U V L R C _ _ _ _ _ _ lc hsound hnoclique A hA
    let F := p.functions lc (A : Set _)
    have hF : ∀ q, LipschitzWith 64 (F q) := p.functions_lipschitz lc A
    have hb : ∀ q x, |F q x| ≤ 1 := p.functions_bounded lc A
    have hodd : ∀ q x, F q (fun z => x z + ((1/2:ℝ):Circle)) = -F q x :=
      p.functions_odd lc A
    obtain ⟨rule,Hrule⟩ := HJ U V L R n F hF hb m hm
    let rules := ruleUnion rule
    let lists (chain : Fin n → C) (I : Finset (Fin (n+1))) :=
      terminalList lc chain I (rules I (chainView lc chain I))
    have hrcard (I : Finset (Fin (n+1))) (hI : Small s I) (v : SubchainView U V L R n I) :
        (rules I v).card ≤ d := by
      change (ruleUnion rule I v).card ≤ d
      simp only [ruleUnion, dite_eq_left hI]
      exact (Hrule I hI v).2.trans (le_max_right _ _)
    have hlcard (chain : Fin n → C) (I : Finset (Fin (n+1))) (hI : Small s I) :
        (lists chain I).card ≤ d :=
      Finset.card_image_le.trans (hrcard I hI (chainView lc chain I))
    have hbad : (𝔼 chain : Fin n → C, (μ.badMass (lists chain) : ℝ)) ≤
        ε + 4^(n+1)*(d:ℝ)^2*σ := by
      have hm' : ∀ W : Finset (Fin (n+1)) → Finset (MixedTuple L R n n),
          (∀ I, Small s I → (W I).card ≤ d) → ListsSeparated (s:=s) W → (μ.badMass W : ℝ) ≤ ε := by
        intro W hc hsep
        exact hμ (MixedTuple L R n n) W hc hsep
      exact good_pair_probability μ hε.le (by exact_mod_cast hσ.le) hm' lists hlcard
        (fun I J hI hJ hsep => source_lists_probability lc hsound rules hrcard I J hI hJ hsep)
    have hbad2 : (𝔼 chain : Fin n → C, ∑ B,
        (μ.supported.weight B : ℝ) * (if ¬Aligned (lists chain) B.val then 1 else 0)) ≤ 2*ε := by
      have hbeq : (𝔼 chain : Fin n → C, ∑ B,
          (μ.supported.weight B : ℝ) * (if ¬Aligned (lists chain) B.val then 1 else 0)) =
          𝔼 chain : Fin n → C, (μ.badMass (lists chain) : ℝ) := by
        apply Finset.expect_congr rfl
        intro chain _
        exact μ.bad_supported (lists chain)
      rw [hbeq]
      linarith
    have hgood (chain : Fin n → C) (B : {B : Finset (Fin (n+1)) // B.card = s})
        (h : ¬¬Aligned (lists chain) B.val) :
        fiberSquare lc chain F B.val (supported_nonempty hs0 B) m ρ k ≤ 6*ε := by
      have herr : (0:ℝ) ≤ 2*64/(m*2^k:ℕ) := by positivity
      have herrγ : (2*64:ℝ)/(m*2^k:ℕ) < γ := by exact_mod_cast hD
      have hkgrid : (2*64:ℝ)*s*(1/2:ℝ)^k < ε := by
        convert hgrid using 1
        simp
        ring
      exact (HT m s k ρ γ (2*64/(m*2^k:ℕ)) hm hs (by exact_mod_cast hρ.le)
        herr herrγ hstep hrare hρK hzero hkgrid U V L R C n lc chain F hF hb hodd
        (fun i j hij y => p.functions_compatibility lc hnoclique A hA chain i j hij y)
        rule (fun I hI v t => ((Hrule I hI v).1 t).2)
        B.val (supported_nonempty hs0 B) B.property (Classical.not_not.mp h)).le
    apply density_from_good_fibers μ.supported
      (fun chain B => ¬Aligned (lists chain) B.val)
      (fun chain B => fiberSquare lc chain F B.val (supported_nonempty hs0 B) m ρ k)
      hε.le (by dsimp [ε]; linarith) (by
        calc
          _ = (𝔼 chain : Fin n → C, ∑ B, (μ.supported.weight B : ℝ) *
            (if ¬Aligned (lists chain) B.val then 1 else 0)) := by
              apply Finset.expect_congr rfl
              intro chain _
              apply Finset.sum_congr rfl
              intro B _
              by_cases h : Aligned (lists chain) B.val <;> simp [h]
          _ ≤ 2*ε := hbad2) hgood
      (fun chain B => fiberSquare_le_one lc chain F hb B.val (supported_nonempty hs0 B) m k
        (by exact_mod_cast hρ.le)) A
    exact p.density_le_fibers lc hnoclique A hA

end LargeIndependentSets

end OAI
