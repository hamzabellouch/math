import OAI.Analysis.SeparableQuotients.RealCoefficients

namespace OAI

noncomputable section

namespace SeparableQuotient.PathSelection
open Filter
open scoped Topology Classical
universe u

/-- A finite threshold selection procedure for quantitative overlap bounds. -/
lemma threshold_selection {Λ : Type u} (f : Λ → ℕ → ℝ) (M δ : ℝ)
    (hM : ∀ a n, |f a n| ≤ M) (N : ℕ)
    (hcap : ∀ (s : Finset Λ) (φ : ℕ → ℕ), StrictMono φ →
      (∀ a ∈ s, ∀ n, δ < |f a (φ n)|) → s.card ≤ N) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ a, CauchySeq (fun n => f a (φ n)) ∨ ∀ᶠ n in atTop, |f a (φ n)| ≤ δ := by
  let Attain : ℕ → Prop := fun k => ∃ (s : Finset Λ) (φ : ℕ → ℕ),
    s.card = k ∧ StrictMono φ ∧ ∀ a ∈ s,
      CauchySeq (fun n => f a (φ n)) ∧ ∀ n, δ < |f a (φ n)|
  have hzero : Attain 0 := ⟨∅, id, by simp, strictMono_id, by simp⟩
  let k := Nat.findGreatest Attain N
  obtain ⟨s, φ, hcard, hφ, hs⟩ := Nat.findGreatest_spec (P := Attain) (Nat.zero_le N) hzero
  refine ⟨φ, hφ, fun a => ?_⟩
  by_cases has : a ∈ s
  · exact Or.inl (hs a has).1
  · by_contra! bad
    have hfreq : ∃ᶠ n in atTop, δ < |f a (φ n)| := by
      simpa only [not_le] using bad.2
    obtain ⟨ψ, hψ, hψδ⟩ := extraction_of_frequently_atTop hfreq
    obtain ⟨y, _, χ, hχ, htχ⟩ := isCompact_Icc.tendsto_subseq
      (s := Set.Icc (-M) M) (x := fun n => f a (φ (ψ n)))
      (fun n => abs_le.mp (hM a (φ (ψ n))))
    let η : ℕ → ℕ := φ ∘ ψ ∘ χ
    have hη : StrictMono η := hφ.comp (hψ.comp hχ)
    have hnew : Attain (k+1) := by
      refine ⟨insert a s, η, ?_, hη, ?_⟩
      · rw [Finset.card_insert_of_notMem has, hcard]
      · intro b hb
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact ⟨htχ.cauchySeq, fun n => hψδ (χ n)⟩
        · exact ⟨(hs b hb).1.comp_tendsto ((hψ.comp hχ).tendsto_atTop),
            fun n => (hs b hb).2 (ψ (χ n))⟩
    have hbound : k+1 ≤ N := by
      obtain ⟨t, η, ht, hη, hh⟩ := hnew
      rw [← ht]
      exact hcap t η hη (fun b hb => (hh b hb).2)
    have := Nat.le_findGreatest (P := Attain) hbound hnew
    change k+1 ≤ k at this
    omega

end SeparableQuotient.PathSelection

namespace SeparableQuotient.PathSelection
open Filter
open scoped Topology Classical

/-- A genuinely nested sequence of subsequences, with the usual diagonal map. -/
structure Nested where
  seq : ℕ → ℕ → ℕ
  mono : ∀ k, StrictMono (seq k)
  nested : ∀ k, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ seq (k+1) = seq k ∘ ψ

def Nested.diag (A : Nested) : ℕ → ℕ := fun n => A.seq n n

lemma Nested.represent (A : Nested) {k n : ℕ} (hn : k ≤ n) (i : ℕ) :
    ∃ j ≥ i, A.seq n i = A.seq k j := by
  induction hn generalizing i with
  | refl => exact ⟨i, le_rfl, rfl⟩
  | @step n hn ih =>
    obtain ⟨ψ, hψ, he⟩ := A.nested n
    obtain ⟨j, hj, hij⟩ := ih (ψ i)
    exact ⟨j, (hψ.id_le i).trans hj, by simpa only [he, Function.comp_apply] using hij⟩

lemma Nested.diag_strictMono (A : Nested) : StrictMono A.diag := by
  apply strictMono_nat_of_lt_succ
  intro n
  obtain ⟨ψ, hψ, he⟩ := A.nested n
  change A.seq n n < A.seq (n+1) (n+1)
  rw [he, Function.comp_apply]
  exact (A.mono n) ((Nat.lt_succ_self n).trans_le (hψ.id_le (n+1)))

lemma Nested.eventually_diag (A : Nested) {P : ℕ → Prop} (k : ℕ)
    (h : ∀ᶠ i in atTop, P (A.seq k i)) : ∀ᶠ n in atTop, P (A.diag n) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  filter_upwards [eventually_ge_atTop (max k N)] with n hn
  obtain ⟨j, hj, he⟩ := A.represent ((le_max_left k N).trans hn) n
  change P (A.seq n n)
  rw [he]
  exact hN j ((le_max_right k N).trans (hn.trans hj))

lemma Nested.cauchy_diag {X : Type*} [PseudoMetricSpace X] (A : Nested) (f : ℕ → X)
    (k : ℕ) (h : CauchySeq (f ∘ A.seq k)) : CauchySeq (f ∘ A.diag) := by
  rw [Metric.cauchySeq_iff] at h ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨max k N, fun m hm n hn => ?_⟩
  obtain ⟨i, hi, he⟩ := A.represent ((le_max_left k N).trans hm) m
  obtain ⟨j, hj, hf⟩ := A.represent ((le_max_left k N).trans hn) n
  change dist (f (A.seq m m)) (f (A.seq n n)) < ε
  rw [he, hf]
  exact hN i ((le_max_right k N).trans (hm.trans hi)) j ((le_max_right k N).trans (hn.trans hj))

end SeparableQuotient.PathSelection

namespace SeparableQuotient.PathSelection
open Filter
open scoped Topology Classical
universe u

/-- Simultaneous convergence on an arbitrary, possibly uncountable, path family.
Only finite quantitative overlap bounds are required. -/
lemma simultaneous_cauchy {Λ : Type u} (f : Λ → ℕ → ℝ) (M : ℝ)
    (hM : ∀ a n, |f a n| ≤ M)
    (hcap : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ,
      ∀ (s : Finset Λ) (φ : ℕ → ℕ), StrictMono φ →
        (∀ a ∈ s, ∀ n, δ < |f a (φ n)|) → s.card ≤ N) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ a, CauchySeq (fun n => f a (φ n)) := by
  let δ : ℕ → ℝ := fun n => 1/((n+1 : ℕ) : ℝ)
  have hδ : ∀ n, 0 < δ n := by intro n; dsimp [δ]; positivity
  let Subseq := {φ : ℕ → ℕ // StrictMono φ}
  have hex : ∀ n (u : Subseq), ∃ v : Subseq,
      (∀ a, CauchySeq (fun i => f a (v.val i)) ∨
        ∀ᶠ i in atTop, |f a (v.val i)| ≤ δ n) ∧
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ v.val = u.val ∘ ψ := by
    intro n u
    obtain ⟨N, hN⟩ := hcap (δ n) (hδ n)
    obtain ⟨ψ, hψ, hgood⟩ := threshold_selection (fun a i => f a (u.val i)) M (δ n)
      (fun a i => hM a (u.val i)) N
      (fun s φ hφ hh => hN s (u.val ∘ φ) (u.property.comp hφ) hh)
    exact ⟨⟨u.val ∘ ψ, u.property.comp hψ⟩, hgood, ψ, hψ, rfl⟩
  choose next hnext using hex
  let U : ℕ → Subseq := Nat.rec ⟨id, strictMono_id⟩ (fun n u => next n u)
  let A : Nested := {
    seq := fun n => (U n).val
    mono := fun n => (U n).property
    nested := fun n => (hnext n (U n)).2 }
  refine ⟨A.diag, A.diag_strictMono, fun a => ?_⟩
  by_cases hex : ∃ k, CauchySeq (fun n => f a (A.seq k n))
  · obtain ⟨k, hk⟩ := hex
    exact A.cauchy_diag (f a) k hk
  · have hsmall (k : ℕ) : ∀ᶠ n in atTop, |f a (A.diag n)| ≤ δ k := by
      apply A.eventually_diag (P := fun i => |f a i| ≤ δ k) (k+1)
      exact ((hnext k (U k)).1 a).resolve_left (fun h => hex ⟨k+1, h⟩)
    have ht : Tendsto (fun n => f a (A.diag n)) atTop (𝓝 0) := by
      apply Metric.tendsto_nhds.mpr
      intro ε hε
      have hδ0 : Tendsto δ atTop (𝓝 0) :=
        (tendsto_add_atTop_iff_nat 1).mpr tendsto_one_div_atTop_nhds_zero_nat
      obtain ⟨k, hk⟩ := (hδ0.eventually (gt_mem_nhds hε)).exists
      filter_upwards [hsmall k] with n hn
      simpa only [Real.dist_eq, sub_zero] using hn.trans_lt hk
    exact ht.cauchySeq

end SeparableQuotient.PathSelection

namespace SeparableQuotient.PathSelection
open Filter
open scoped Topology

lemma power_cap (r M δ : ℝ) (hr : r < 1) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, δ * n ≤ M * (n : ℝ)^r → n ≤ N := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ)^(1-r)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < 1-r)).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (eventually_gt_atTop (M/δ)))
  refine ⟨N, fun n hn => ?_⟩
  by_contra hbad
  have hnN : N < n := Nat.lt_of_not_ge hbad
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hp : 0 < (n : ℝ)^r := Real.rpow_pos_of_pos hn0 _
  have hm : M < δ * (n : ℝ)^(1-r) := (div_lt_iff₀ hδ).mp (hN n hnN.le)
    |>.trans_eq (mul_comm _ _)
  have he : (n : ℝ)^r * (n : ℝ)^(1-r) = n := by
    rw [← Real.rpow_add hn0, add_sub_cancel, Real.rpow_one]
  have := mul_lt_mul_of_pos_left hm hp
  rw [mul_left_comm, he] at this
  nlinarith

end SeparableQuotient.PathSelection

namespace SeparableQuotient.Norming
open PathCoding
open scoped Classical

/-- Paths are indexed by their full raw data, not by an arbitrary chosen
expression witnessing membership. The witness is retained when used. -/
def PathIndex (f : Family) := {r : RawPath // ∃ P : InfinitePath f, P.raw = r}

def PathIndex.repr {f : Family} (a : PathIndex f) : InfinitePath f := a.property.choose

@[simp] lemma PathIndex.repr_raw {f : Family} (a : PathIndex f) : a.repr.raw = a.val :=
  a.property.choose_spec

lemma PathIndex.repr_injective {f : Family} : Function.Injective
    (fun a : PathIndex f => a.repr.raw) := by
  intro a b hab
  apply Subtype.ext
  simpa only [PathIndex.repr_raw] using hab

end SeparableQuotient.Norming

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding Filter
open scoped Classical Topology

@[reducible] local instance dualEGroup10 : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
@[reducible] local instance dualESpace10 : NormedSpace ℝ (StrongDual ℝ E) := inferInstance

lemma real_tail_bound {f : Family} {h : ℕ} (P : Fin h → InfinitePath f) (N : ℕ)
    (hdis : Pairwise (fun i j => Disjoint
      (Set.range (fun n => (P i).raw.weight (n+N+1)))
      (Set.range (fun n => (P j).raw.weight (n+N+1)))))
    (c : Fin h → ℝ) :
    ‖∑ i, c i • pathTail (P i) N‖ ≤ (∑ i, |c i| ^ f.q) ^ (1/f.q) := by
  have hq : 0 < f.q := lt_trans zero_lt_one (Parameters.q_bounds f.s_ge_two).1
  apply RealCoefficients.bound_from_unit f.q hq (fun i => pathTail (P i) N)
  intro a ha
  exact RealCoefficients.rational_to_real f.q hq (fun i => pathTail (P i) N)
    (rational_tail_bound P N hdis) a ha

lemma exists_tail_estimate {f : Family} {h : ℕ} (P : Fin h → InfinitePath f)
    (hinj : Function.Injective (fun i => (P i).raw)) :
    ∃ N, ∀ c : Fin h → ℝ,
      ‖∑ i, c i • pathTail (P i) N‖ ≤ (∑ i, |c i| ^ f.q) ^ (1/f.q) := by
  obtain ⟨N, hN⟩ := RawPath.Admissible.disjoint_weight_tails
    (fun i => (P i).raw) (fun i => (P i).admissible) hinj
  refine ⟨N, real_tail_bound P N ?_⟩
  intro i j hij
  apply (hN hij).mono
  · rintro w ⟨n, rfl⟩
    exact ⟨n+1, by change (P i).raw.weight ((n+1)+N) = (P i).raw.weight (n+N+1); congr 1; omega⟩
  · rintro w ⟨n, rfl⟩
    exact ⟨n+1, by change (P j).raw.weight ((n+1)+N) = (P j).raw.weight (n+N+1); congr 1; omega⟩

lemma tail_abs_sum_bound {f : Family} {h : ℕ} (P : Fin h → InfinitePath f) (N : ℕ)
    (hN : ∀ c : Fin h → ℝ,
      ‖∑ i, c i • pathTail (P i) N‖ ≤ (∑ i, |c i| ^ f.q) ^ (1/f.q)) (x : E) :
    (∑ i, |pathTail (P i) N x|) ≤ (h : ℝ) ^ (1/f.q) * ‖x‖ := by
  let c : Fin h → ℝ := fun i => RealCoefficients.signChoice (pathTail (P i) N x)
  have hc (i : Fin h) : |c i| = 1 := RealCoefficients.abs_signChoice _
  have hv (i : Fin h) : c i * pathTail (P i) N x = |pathTail (P i) N x| :=
    RealCoefficients.signChoice_mul _
  have he : (∑ i, c i • pathTail (P i) N) x = ∑ i, |pathTail (P i) N x| := by
    simp only [sum_apply, smul_apply, smul_eq_mul, hv]
  calc
    _ = |(∑ i, c i • pathTail (P i) N) x| := by
      rw [he, abs_of_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _))]
    _ ≤ ‖∑ i, c i • pathTail (P i) N‖ * ‖x‖ :=
      by simpa only [Real.norm_eq_abs] using (∑ i, c i • pathTail (P i) N).le_opNorm x
    _ ≤ _ := mul_le_mul_of_nonneg_right (by simpa only [hc, Real.one_rpow,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] using hN c)
      (norm_nonneg _)

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

/-- Bounded blocks are null on the coordinate predual. This intermediate
property is stated separately so that the path argument works for any such
sequence, not just a chosen block representation. -/
def PredualNull (x : ℕ → E) : Prop :=
  ∀ y : X₀, Tendsto (fun n => y.val (x n)) atTop (𝓝 0)

lemma path_threshold_cap {f : Family} (x : ℕ → E) (M : ℝ)
    (hM : ∀ n, ‖x n‖ ≤ M) (hx : PredualNull x) (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℕ, ∀ (s : Finset (PathIndex f)) (φ : ℕ → ℕ), StrictMono φ →
      (∀ a ∈ s, ∀ n, δ < |pathFunctional a.repr (x (φ n))|) → s.card ≤ K := by
  have hq : 1 < f.q := (Parameters.q_bounds f.s_ge_two).1
  obtain ⟨K, hK⟩ := PathSelection.power_cap (1/f.q) M (δ/2)
    ((div_lt_one (by linarith)).mpr (by linarith)) (by linarith)
  refine ⟨K, fun s φ hφ hs => ?_⟩
  let e : Fin s.card ≃ s := s.equivFin.symm
  let P : Fin s.card → InfinitePath f := fun i => (e i).val.repr
  have hinj : Function.Injective (fun i => (P i).raw) := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    exact PathIndex.repr_injective hij
  obtain ⟨N, hN⟩ := exists_tail_estimate P hinj
  have hsmall (i : Fin s.card) : ∀ᶠ n in atTop,
      |pathFunctional (P i) (x (φ n)) - pathTail (P i) N (x (φ n))| < δ/2 := by
    have ht := (hx ⟨pathFunctional (P i) - pathTail (P i) N,
      pathTail_complement_mem (P i) N⟩).comp hφ.tendsto_atTop
    have hδ0 : |(0 : ℝ)| < δ/2 := by rw [abs_zero]; exact half_pos hδ
    have he := ht.abs.eventually (gt_mem_nhds hδ0)
    simpa only [Function.comp_apply, sub_apply, abs_zero] using he
  obtain ⟨n, hn⟩ := (eventually_all_finset (I := Finset.univ)).mpr
    (fun i _ => hsmall i) |>.exists
  have hlower (i : Fin s.card) : δ/2 ≤ |pathTail (P i) N (x (φ n))| := by
    have hh := hs (e i).val (e i).property n
    have hh' := hn i (Finset.mem_univ i)
    have ht := abs_sub_abs_le_abs_sub
      (pathFunctional (P i) (x (φ n))) (pathTail (P i) N (x (φ n)))
    dsimp only [P] at ht hh'
    linarith
  apply hK s.card
  calc
    δ/2 * (s.card : ℝ) = ∑ _i : Fin s.card, δ/2 := by simp [mul_comm]
    _ ≤ ∑ i, |pathTail (P i) N (x (φ n))| := Finset.sum_le_sum (fun i _ => hlower i)
    _ ≤ (s.card : ℝ)^(1/f.q) * ‖x (φ n)‖ := tail_abs_sum_bound P N hN _
    _ ≤ M * (s.card : ℝ)^(1/f.q) := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hM (φ n))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)

lemma path_all_cauchy {f : Family} (x : ℕ → E) (M : ℝ)
    (hM : ∀ n, ‖x n‖ ≤ M) (hx : PredualNull x) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ a : PathIndex f,
      CauchySeq (fun n => pathFunctional a.repr (x (φ n))) := by
  apply PathSelection.simultaneous_cauchy (fun (a : PathIndex f) (n : ℕ) =>
    pathFunctional a.repr (x n)) M
  · intro a n
    simpa only [Real.norm_eq_abs] using
      (PathLimits.unit_bound _ (norm_pathFunctional_le a.repr) _).trans (hM n)
  · exact path_threshold_cap x M hM hx

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.DenseZero
open Filter
open scoped Topology
universe u
variable {Z : Type u} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

lemma tendsto_zero_of_dense (g : ℕ → StrongDual ℝ Z) (M : ℝ)
    (hM : ∀ n, ‖g n‖ ≤ M) (D : Set Z) (hD : Dense D)
    (h : ∀ z ∈ D, Tendsto (fun n => g n z) atTop (𝓝 0)) (z : Z) :
    Tendsto (fun n => g n z) atTop (𝓝 0) := by
  have hM0 : 0 ≤ M := (norm_nonneg (g 0)).trans (hM 0)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨w, hw, hzw⟩ := Metric.mem_closure_iff.mp (hD z) (ε/(2*(M+1))) (by positivity)
  have he := (Metric.tendsto_nhds.mp (h w hw) (ε/2) (by linarith))
  filter_upwards [he] with n hn
  have hdist : dist (g n z) (g n w) ≤ M * dist z w := by
    rw [dist_eq_norm, ← map_sub, dist_eq_norm]
    exact ((g n).le_opNorm (z-w)).trans
      (mul_le_mul_of_nonneg_right (hM n) (norm_nonneg _))
  have hsmall : M * dist z w < ε/2 := by
    have hd : dist z w < ε/(2*(M+1)) := by simpa only [dist_comm] using hzw
    have hdm : (M+1) * dist z w < ε/2 := by
      have hh := (lt_div_iff₀ (by positivity : 0 < 2*(M+1))).mp hd
      nlinarith
    have hle : M * dist z w ≤ (M+1) * dist z w :=
      mul_le_mul_of_nonneg_right (by linarith) (dist_nonneg : 0 ≤ dist z w)
    exact hle.trans_lt hdm
  exact (dist_triangle (g n z) (g n w) 0).trans_lt (by linarith)

end SeparableQuotient.DenseZero

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

@[reducible] local instance dualEGroup11 : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
@[reducible] local instance dualESpace11 : NormedSpace ℝ (StrongDual ℝ E) := inferInstance
@[reducible] local instance predualGroup11 : NormedAddCommGroup X₀ := inferInstance
@[reducible] local instance predualSpace11 : NormedSpace ℝ X₀ := inferInstance
@[reducible] local instance dualPredualGroup11 : NormedAddCommGroup (StrongDual ℝ X₀) := inferInstance
@[reducible] local instance dualPredualSpace11 : NormedSpace ℝ (StrongDual ℝ X₀) := inferInstance

lemma predualNull_of_coordinates (x : ℕ → E) (M : ℝ)
    (hM : ∀ n, ‖x n‖ ≤ M)
    (hx : ∀ a : Γ, Tendsto (fun n => coordinate a (x n)) atTop (𝓝 0)) :
    PredualNull x := by
  let V : Submodule ℝ X₀ := {
    carrier := {y | Tendsto (fun n => y.val (x n)) atTop (𝓝 0)}
    zero_mem' := by simp
    add_mem' := by
      intro y z hy hz
      change Tendsto (fun n => (y.val + z.val) (x n)) atTop (𝓝 0)
      simpa only [add_apply, add_zero] using hy.add hz
    smul_mem' := by
      intro c y hy
      change Tendsto (fun n => (c • y.val) (x n)) atTop (𝓝 0)
      simpa only [smul_apply, smul_zero] using hy.const_smul c }
  have hspan : Submodule.span ℝ (Set.range coordinate₀) ≤ V := by
    apply Submodule.span_le.mpr
    rintro y ⟨a, rfl⟩
    exact hx a
  intro y
  exact DenseZero.tendsto_zero_of_dense (fun n => norming.evaluation (x n)) M
    (fun n => (norming.norm_evaluation (x n)).le.trans (hM n))
    (Submodule.span ℝ (Set.range coordinate₀)) dense_span_coordinate₀
    (fun z hz => hspan hz) y

/-- Admissible block sequences with real coefficients. Pure mode requires one color, mixed mode both orders. -/
structure BlockSequence (f : Family) where
  vector : ℕ → Γ →₀ ℝ
  nonzero : ∀ n, vector n ≠ 0
  successive : ∀ i j, i < j → ∀ a ∈ (vector i).support, ∀ b ∈ (vector j).support,
    a < b ∧ (f = .mixed → Colors.color a < Colors.color b)
  pure_color : ∀ k, f = .pure k → ∀ n a, a ∈ (vector n).support → Colors.color a = k

def BlockSequence.embed {f : Family} (x : BlockSequence f) (n : ℕ) : E :=
  norming.includeFinite (x.vector n)

lemma BlockSequence.coordinate_eventually_zero {f : Family} (x : BlockSequence f) (a : Γ) :
    ∀ᶠ n in atTop, coordinate a (x.embed n) = 0 := by
  by_cases hex : ∃ n, x.vector n a ≠ 0
  · obtain ⟨i, hi⟩ := hex
    filter_upwards [eventually_ge_atTop (i+1)] with n hn
    change norming.coordinate a (norming.includeFinite (x.vector n)) = 0
    rw [norming.coordinate_includeFinite]
    by_contra h
    exact (lt_irrefl a) (x.successive i n (by omega) a (Finsupp.mem_support_iff.mpr hi)
      a (Finsupp.mem_support_iff.mpr h)).1
  · push Not at hex
    apply Eventually.of_forall
    intro n
    exact (norming.coordinate_includeFinite a (x.vector n)).trans (hex n)

lemma BlockSequence.predualNull {f : Family} (x : BlockSequence f) (M : ℝ)
    (hM : ∀ n, ‖x.embed n‖ ≤ M) : PredualNull x.embed := by
  apply predualNull_of_coordinates x.embed M hM
  intro a
  exact tendsto_const_nhds.congr' ((x.coordinate_eventually_zero a).mono fun _ h => h.symm)

lemma pathFunctional_eq_of_raw {f : Family} {P Q : InfinitePath f} (h : P.raw = Q.raw) :
    pathFunctional P = pathFunctional Q := by
  ext x
  apply tendsto_nhds_unique (pathPartial_tendsto P x)
  apply (pathPartial_tendsto Q x).congr'
  apply Eventually.of_forall
  intro n
  simp only [pathPartial, ← norming.evaluateArray_eq_functional]
  congr 1
  change (∑ i : Fin (n+1), Q.raw.piece i) = ∑ i : Fin (n+1), P.raw.piece i
  rw [h]

/-- Every bounded block sequence has a subsequence on which every path functional converges. -/
lemma BlockSequence.all_paths_cauchy {f : Family} (x : BlockSequence f) (M : ℝ)
    (hM : ∀ n, ‖x.embed n‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ P : InfinitePath f,
      CauchySeq (fun n => pathFunctional P (x.embed (φ n))) := by
  obtain ⟨φ, hφ, hp⟩ := path_all_cauchy x.embed M hM (x.predualNull M hM)
  refine ⟨φ, hφ, fun P => ?_⟩
  let a : PathIndex f := ⟨P.raw, P, rfl⟩
  have he : pathFunctional a.repr = pathFunctional P := pathFunctional_eq_of_raw a.repr_raw
  simpa only [he] using hp a

end SeparableQuotient.ActualSpace

end

end OAI
