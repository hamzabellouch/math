import Mathlib
import OAI.Analysis.SymmetricDomains.SemialgebraicSelectionAnalyticPath
import OAI.Analysis.SymmetricDomains.PolynomialSignSetChoice2
import OAI.Analysis.SymmetricDomains.PolynomialSignSetOffset

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
namespace Release061.SignElimination
open Set Metric
open scoped Classical

lemma polynomialSignSet_bounded_inward_selection {X ι κ : Type*} [Fintype κ]
    {c : X → ι → ℝ} (A : X → Set (κ → ℝ))
    (hA : PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2)
      {z | z.2 ∈ A z.1}) (S : Set X) (hS : PolynomialSignSet c S)
    (q : MvPolynomial ι ℝ) (hq : ∀ x ∈ S, 0 < MvPolynomial.eval (c x) q)
    (hclosure : ∀ x ∈ S, (0 : κ → ℝ) ∈ closure (A x)) :
    ∃ f : X → κ → ℝ,
      (∀ x ∈ S, f x ∈ A x ∧ ‖f x‖ < MvPolynomial.eval (c x) q) ∧
      PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2)
        {z | z.1 ∈ S ∧ z.2 = f z.1} := by
  let d := fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2
  have hs : PolynomialSignSet d {z | z.1 ∈ S} :=
    hS.coordinate_preimage Prod.fst Sum.inl (by intros; rfl)
  have hn : PolynomialSignSet d
      {z | ‖z.2‖ < MvPolynomial.eval (c z.1) q} := by
    convert PolynomialSignSet.norm_lt_polynomial (c := d)
      (fun k => MvPolynomial.X (Sum.inr k)) (MvPolynomial.rename Sum.inl q) using 1
    ext z
    simp only [mem_ofPred_eq,MvPolynomial.eval_X,MvPolynomial.eval_rename]
    rfl
  let R : Set (X × (κ → ℝ)) := {z | (z.1 ∈ S ∧ z.2 ∈ A z.1) ∧
    ‖z.2‖ < MvPolynomial.eval (c z.1) q}
  have hR : PolynomialSignSet d R := (hs.inter hA).inter hn
  have hdom (x : X) : (∃ y, (x,y) ∈ R) ↔ x ∈ S := by
    constructor
    · rintro ⟨y,⟨hx,_⟩,_⟩
      exact hx
    · intro hx
      obtain ⟨y,hy,hyn⟩ := Metric.mem_closure_iff.mp (hclosure x hx) _ (hq x hx)
      exact ⟨y,⟨hx,hy⟩,by simpa only [dist_zero_left] using hyn⟩
  obtain ⟨f,hf,hfg⟩ := polynomialSignSet_choice_finite hR
  refine ⟨f,fun x hx => ?_,?_⟩
  · have hfx := hf x ((hdom x).mpr hx)
    exact ⟨hfx.1.2,hfx.2⟩
  · convert hfg using 1
    ext z
    simp only [mem_ofPred_eq,hdom]

end Release061.SignElimination

namespace Release061
open Set Filter Topology Metric MeasureTheory Classical
open SignElimination

theorem isSemialgebraic_iff_polynomialSignSet {n : ℕ} {S : Set (Affine n)} :
    IsSemialgebraic S ↔ PolynomialSignSet realCoordinates S := by
  constructor
  · intro h
    induction h with
    | zero p => exact .zero p
    | positive p => exact .positive p
    | compl _ ih => exact ih.compl
    | union _ _ ih ih' => exact ih.union ih'
  · intro h
    induction h with
    | zero p => exact .zero p
    | positive p => exact .positive p
    | compl _ ih => exact ih.compl
    | union _ _ ih ih' => exact ih.union ih'

lemma real_polynomial_zero_null {n : ℕ} (D : MvPolynomial (Fin n) ℝ) (hD : D ≠ 0) :
    volume {s : Fin n → ℝ | MvPolynomial.eval s D = 0} = 0 := by
  have hmap := (MvPolynomial.map_injective (σ := Fin n) Complex.ofRealHom
    Complex.ofReal_injective).ne hD
  have hn := complex_polynomial_real_zero_null
    (MvPolynomial.map Complex.ofRealHom D) (by simpa only [map_zero] using hmap)
  have he : {s : Fin n → ℝ |
      MvPolynomial.eval (fun i => (s i : ℂ)) (MvPolynomial.map Complex.ofRealHom D) = 0} =
      {s : Fin n → ℝ | MvPolynomial.eval s D = 0} := by
    ext s
    change MvPolynomial.eval (realParameter s) (MvPolynomial.map Complex.ofRealHom D) = 0 ↔
      MvPolynomial.eval s D = 0
    rw [complexify_mv_eval,Complex.ofReal_eq_zero]
  rwa [he] at hn

lemma PolynomialSignSet.parameter_strip {n : ℕ} {B : Set (Fin n → ℝ)}
    (hB : PolynomialSignSet id B) (ε : ℝ) :
    PolynomialSignSet id {x : Fin (n+1) → ℝ | Fin.tail x ∈ B ∧ x 0 ∈ Ioo 0 ε} := by
  have hb : PolynomialSignSet id {x : Fin (n+1) → ℝ | Fin.tail x ∈ B} :=
    hB.coordinate_preimage (fun x : Fin (n+1) → ℝ => Fin.tail x) Fin.succ
      (d := id) (by intros; rfl)
  have hp : PolynomialSignSet id {x : Fin (n+1) → ℝ | 0 < x 0} := by
    simpa using (PolynomialSignSet.positive (c := id) (MvPolynomial.X 0))
  have he : PolynomialSignSet id {x : Fin (n+1) → ℝ | x 0 < ε} := by
    have heq : {x : Fin (n+1) → ℝ | x 0 < ε} =
        {x : Fin (n+1) → ℝ | 0 < MvPolynomial.eval (id x)
          (MvPolynomial.C ε-MvPolynomial.X 0)} := by
      ext x
      simp
    rw [heq]
    exact PolynomialSignSet.positive _
  exact hb.inter (hp.inter he)

theorem semialgebraic_boundary_fiber_closure_from_family {n k : ℕ}
    (A : (Fin n → ℝ) → Set (Fin k → ℝ))
    (hA : PolynomialSignSet (fun z : (Fin n → ℝ) × (Fin k → ℝ) => Sum.elim z.1 z.2)
      {z | z.2 ∈ A z.1})
    (B : Set (Fin n → ℝ)) (hB : IsOpen B) (hBs : PolynomialSignSet id B)
    (hb : ∀ s ∈ B, (s,(0 : Fin k → ℝ)) ∈
      closure {p : (Fin n → ℝ) × (Fin k → ℝ) | p.2 ∈ A p.1}) :
    ∃ B' : Set (Fin n → ℝ), IsOpen B' ∧ PolynomialSignSet id B' ∧
      B' ⊆ B ∧ volume (B \ B') = 0 ∧ ∀ s ∈ B', (0 : Fin k → ℝ) ∈ closure (A s) := by
  have hg := polynomialSignSet_inwardDistance_graph (c := id) A hA
  have hbb : PolynomialSignSet
      (fun z : (Fin n → ℝ) × ℝ => fun o => Option.elim o z.2 z.1) {z | z.1 ∈ B} :=
    hBs.coordinate_preimage Prod.fst some (by intros; rfl)
  have hgraph : PolynomialSignSet id
      {x : Option (Fin n) → ℝ | (fun i => x (some i)) ∈ B ∧
        x none = inwardDistance A (fun i => x (some i))} :=
    (hbb.inter hg).coordinate_preimage
      (fun x : Option (Fin n) → ℝ => ((fun i => x (some i)),x none)) id
      (by intro x o; cases o <;> rfl)
  obtain ⟨D,hD,hreg⟩ := semialgebraic_function_analytic_off_polynomial
    B (inwardDistance A) hgraph
  let B' := B ∩ {s | MvPolynomial.eval s D ≠ 0}
  have hopen : IsOpen B' := hB.inter
    ((MvPolynomial.continuous_eval D).isOpen_preimage _ isOpen_ne)
  have hs : PolynomialSignSet id B' := hBs.inter (PolynomialSignSet.zero D).compl
  refine ⟨B',hopen,hs,inter_subset_left,?_,?_⟩
  · apply measure_mono_null _ (real_polynomial_zero_null D hD)
    intro s hs
    by_contra hn
    exact hs.2 ⟨hs.1,hn⟩
  · intro s hs
    exact boundary_fiber_closure_at_continuity A s
      (hreg s hs.1 hs.2).continuousAt (hb s hs.1)

theorem semialgebraic_bounded_selection_from_family {n k : ℕ}
    (A : (Fin n → ℝ) → Set (Fin k → ℝ))
    (hA : PolynomialSignSet (fun z : (Fin n → ℝ) × (Fin k → ℝ) => Sum.elim z.1 z.2)
      {z | z.2 ∈ A z.1})
    (B : Set (Fin n → ℝ)) (hB : PolynomialSignSet id B) (ε : ℝ)
    (hc : ∀ s ∈ B, (0 : Fin k → ℝ) ∈ closure (A s)) :
    ∃ v : (Fin (n+1) → ℝ) → (Fin k → ℝ),
      (∀ j, PolynomialSignSet id
        {x : Option (Fin (n+1)) → ℝ |
          ((fun i => x (some i.succ)) ∈ B ∧ x (some 0) ∈ Ioo 0 ε) ∧
            x none = v (fun i => x (some i)) j}) ∧
      ∀ x : Fin (n+1) → ℝ, Fin.tail x ∈ B → x 0 ∈ Ioo 0 ε →
        v x ∈ A (Fin.tail x) ∧ ‖v x‖ < x 0 := by
  let A' : (Fin (n+1) → ℝ) → Set (Fin k → ℝ) := fun x => A (Fin.tail x)
  have ha : PolynomialSignSet
      (fun z : (Fin (n+1) → ℝ) × (Fin k → ℝ) => Sum.elim z.1 z.2)
      {z | z.2 ∈ A' z.1} :=
    hA.coordinate_preimage
      (fun z : (Fin (n+1) → ℝ) × (Fin k → ℝ) => (Fin.tail z.1,z.2))
      (Sum.map Fin.succ id) (by intro z i; cases i <;> rfl)
  let S : Set (Fin (n+1) → ℝ) := {x | Fin.tail x ∈ B ∧ x 0 ∈ Ioo 0 ε}
  have hs : PolynomialSignSet id S := hB.parameter_strip ε
  obtain ⟨v,hv,hvg⟩ := polynomialSignSet_bounded_inward_selection (c := id) A' ha S hs
    (MvPolynomial.X 0) (fun x hx => by simpa using hx.2.1)
    (fun x hx => hc (Fin.tail x) hx.1)
  refine ⟨v,fun j => ?_,fun x hx ht => ?_⟩
  · have hj := polynomialSignSet_vector_graph_coordinate hvg j
    exact hj.coordinate_preimage
      (fun x : Option (Fin (n+1)) → ℝ => ((fun i => x (some i)),x none)) id
      (by intro x o; cases o <;> rfl)
  · simpa only [A',MvPolynomial.eval_X,id_eq] using hv x ⟨hx,ht⟩

theorem semialgebraic_inward_analytic_from_family {n k : ℕ}
    (A : (Fin n → ℝ) → Set (Fin k → ℝ))
    (hA : PolynomialSignSet (fun z : (Fin n → ℝ) × (Fin k → ℝ) => Sum.elim z.1 z.2)
      {z | z.2 ∈ A z.1})
    (B : Set (Fin n → ℝ)) (hB : IsOpen B) (hBs : PolynomialSignSet id B)
    (hb : ∀ s ∈ B, (s,(0 : Fin k → ℝ)) ∈
      closure {p : (Fin n → ℝ) × (Fin k → ℝ) | p.2 ∈ A p.1}) :
    ∃ E : Set (Fin n → ℝ), E ⊆ B ∧ volume E = 0 ∧
      ∀ s ∈ B, s ∉ E → ∃ r > 0, ∃ η > 0,
        ∃ ψ : (Fin n → ℝ) × ℝ → (Fin k → ℝ),
          ball s r ⊆ B ∧ AnalyticOnNhd ℝ ψ (ball s r ×ˢ ball 0 η) ∧
          (∀ x ∈ ball s r, ψ (x,0) = 0) ∧
          ∀ x ∈ ball s r, ∀ t ∈ Ioo (0 : ℝ) η, ψ (x,t) ∈ A x := by
  obtain ⟨B',hB'o,hB's,hB'B,hnull,hc⟩ :=
    semialgebraic_boundary_fiber_closure_from_family A hA B hB hBs hb
  obtain ⟨v,hvg,hv⟩ := semialgebraic_bounded_selection_from_family A hA B' hB's 1 hc
  obtain ⟨E,hEB,hE,H⟩ := semialgebraic_selection_analytic_path hB'o zero_lt_one A v hvg hv
  refine ⟨(B \ B') ∪ E,?_,measure_union_null hnull hE,?_⟩
  · intro x hx
    rcases hx with hx | hx
    · exact hx.1
    · exact hB'B (hEB hx)
  · intro s hs hsE
    have hs' : s ∈ B' := by
      by_contra hn
      exact hsE (Or.inl ⟨hs,hn⟩)
    obtain ⟨r,hr,η,hη,ψ,hrB,hψ,hzero,hAψ⟩ := H s hs' (fun he => hsE (Or.inr he))
    exact ⟨r,hr,η,hη,ψ,hrB.trans hB'B,hψ,hzero,hAψ⟩

theorem semialgebraic_offset_limits_from_family {n k : ℕ}
    (A : (Fin n → ℝ) → Set (Fin k → ℝ))
    (hA : PolynomialSignSet (fun z : (Fin n → ℝ) × (Fin k → ℝ) => Sum.elim z.1 z.2)
      {z | z.2 ∈ A z.1})
    (B : Set (Fin n → ℝ)) (hB : IsOpen B) (hBs : PolynomialSignSet id B)
    (h0 : ∀ s ∈ B, (0 : Fin k → ℝ) ∉ A s) :
    ∃ E : Set (Fin n → ℝ), E ⊆ B ∧ volume E = 0 ∧
      ∀ s ∈ B, s ∉ E → ∃ f : (Fin k → ℝ) → ℝ, LipschitzWith 1 f ∧
        (∀ y, f y ∈ Icc (0 : ℝ) 1) ∧
        (∀ y, Tendsto (fun p : (Fin n → ℝ) × ℝ => offsetDistance A p.1 p.2 y)
          (𝓝[{p : (Fin n → ℝ) × ℝ | 0 < p.2}] (s,0)) (𝓝 (f y))) ∧
        (∀ K : Set (Fin k → ℝ), IsCompact K →
          TendstoUniformlyOn (fun p : (Fin n → ℝ) × ℝ => offsetDistance A p.1 p.2) f
            (𝓝[{p : (Fin n → ℝ) × ℝ | 0 < p.2}] (s,0)) K) ∧
        IsClosed {y | f y = 0} ∧ (0 : Fin k → ℝ) ∈ {y | f y = 0} ∧
        ∀ c : ℝ, 0 < c → ∀ y, f y = 0 ↔ f (c • y) = 0 := by
  apply semialgebraic_offset_limits hB (ε := 1) zero_lt_one A h0
  intro y
  have hg := polynomialSignSet_offsetDistance_graph (c := id) A hA y
  have hgo : PolynomialSignSet id
      {x : Option (Fin (n+1)) → ℝ |
        x none = offsetDistance A (fun i => x (some i.succ)) (x (some 0)) y} :=
    hg.coordinate_preimage
      (fun x : Option (Fin (n+1)) → ℝ => (((fun i => x (some i.succ)),x (some 0)),x none))
      (fun o => Option.elim o none (fun o => Option.elim o (some 0) (fun i => some i.succ)))
      (by intro x o; cases o with | none => rfl | some o => cases o <;> rfl)
  have hs : PolynomialSignSet id
      {x : Option (Fin (n+1)) → ℝ |
        (fun i => x (some i.succ)) ∈ B ∧ x (some 0) ∈ Ioo 0 1} :=
    (hBs.parameter_strip 1).coordinate_preimage (fun x : Option (Fin (n+1)) → ℝ => fun i => x (some i))
      some (by intros; rfl)
  exact hs.inter hgo

end Release061

end

end OAI
