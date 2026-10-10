import Mathlib
import OAI.Probability.LogConcave.Model

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace LogConcaveSampling.OracleCompiler

structure Program (Ω : Type*) [MeasurableSpace Ω] (d q : ℕ)
    (O : Type*) [MeasurableSpace O] where
  query : Fin q → Ω × Transcript d q → Point d
  query_measurable : ∀ i, Measurable (query i)
  output : Ω × Transcript d q → O
  output_measurable : Measurable output

namespace Program
variable {Ω O : Type*} [MeasurableSpace Ω] [MeasurableSpace O] {d q : ℕ}

def history (A : Program Ω d q O) (V : Point d → ℝ) (ω : Ω) : ℕ → Transcript d q
  | 0 => 0
  | n + 1 =>
      let h := A.history V ω n
      if hn : n < q then
        Function.update h ⟨n, hn⟩ (firstOrderReply V (A.query ⟨n, hn⟩ (ω, h)))
      else h

def run (A : Program Ω d q O) (V : Point d → ℝ) (ω : Ω) : O :=
  A.output (ω, A.history V ω q)

def algorithm (A : Program Ω d q (Point d)) : OracleAlgorithm Ω d q where
  query := A.query
  query_measurable := A.query_measurable
  output := A.output
  output_measurable := A.output_measurable

lemma algorithm_history (A : Program Ω d q (Point d)) (V : Point d → ℝ) (ω : Ω) (n : ℕ) :
    A.algorithm.history V ω n = A.history V ω n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [OracleAlgorithm.history, history, ih]
    rfl

lemma algorithm_run (A : Program Ω d q (Point d)) (V : Point d → ℝ) (ω : Ω) :
    A.algorithm.run V ω = A.run V ω := by
  unfold OracleAlgorithm.run run
  rw [algorithm_history]
  rfl

lemma history_tail (A : Program Ω d q O) (V : Point d → ℝ) (ω : Ω)
    (n : ℕ) (i : Fin q) (hi : n ≤ i.val) : A.history V ω n i = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [history]
    split_ifs with hn
    · rw [Function.update_of_ne (by intro h; have H := congrArg Fin.val h; dsimp at H; omega)]
      exact ih (by omega)
    · exact ih (by omega)

lemma history_stable (A : Program Ω d q O) (V : Point d → ℝ) (ω : Ω)
    {m n : ℕ} (hmn : m ≤ n) (i : Fin q) (hi : i.val < m) :
    A.history V ω n i = A.history V ω m i := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    simp only [history]
    split_ifs with hn
    · rw [Function.update_of_ne (by intro h; have H := congrArg Fin.val h; dsimp at H; omega)]
      exact ih
    · exact ih

def mask (n : ℕ) (h : Transcript d q) : Transcript d q :=
  fun i => if i.val < n then h i else 0

lemma prefix_zero (h : Transcript d q) : mask 0 h = 0 := by
  funext i
  simp [mask]

lemma prefix_full (h : Transcript d q) : mask q h = h := by
  funext i
  simp [mask, i.isLt]

lemma prefix_succ (n : ℕ) (hn : n < q) (h : Transcript d q) :
    mask (n+1) h = Function.update (mask n h) ⟨n,hn⟩ (h ⟨n,hn⟩) := by
  funext i
  by_cases hi : i = ⟨n,hn⟩
  · subst i
    simp [mask]
  · rw [Function.update_of_ne hi]
    simp only [mask]
    have hne : i.val ≠ n := by intro he; exact hi (Fin.ext he)
    have he : (i.val < n+1) ↔ (i.val < n) := by omega
    simp only [he]

lemma history_eq_prefix (A : Program Ω d q O) (V : Point d → ℝ) (ω : Ω)
    {n : ℕ} (hn : n ≤ q) : A.history V ω n = mask n (A.history V ω q) := by
  funext i
  simp only [mask]
  split_ifs with hi
  · exact (A.history_stable V ω hn i hi).symm
  · exact A.history_tail V ω n i (by omega)

lemma history_spec (A : Program Ω d q O) (V : Point d → ℝ) (ω : Ω) (i : Fin q) :
    A.history V ω q i =
      firstOrderReply V (A.query i (ω, mask i.val (A.history V ω q))) := by
  rw [A.history_stable V ω (m := i.val+1) (by omega) i (by omega)]
  rw [history, dite_eq_left i.isLt]
  simp only [Function.update_self]
  rw [A.history_eq_prefix V ω (by omega)]

lemma history_unique (A : Program Ω d q O) (V : Point d → ℝ) (ω : Ω)
    (h : Transcript d q)
    (hh : ∀ i, h i = firstOrderReply V (A.query i (ω, mask i.val h))) :
    A.history V ω q = h := by
  have hp : ∀ n ≤ q, A.history V ω n = mask n h := by
    intro n hn
    induction n with
    | zero => simp [history, prefix_zero]
    | succ n ih =>
      have hnq : n < q := by omega
      rw [history, dite_eq_left hnq, ih (by omega), prefix_succ n hnq h, hh ⟨n,hnq⟩]
  simpa only [prefix_full] using hp q le_rfl

lemma measurable_prefix (n : ℕ) : Measurable (mask (d:=d) (q:=q) n) := by
  apply Measurable.of_eval
  intro i
  dsimp [mask]
  split_ifs
  · exact measurable_pi_apply i
  · exact measurable_const

lemma measurable_history (A : Program Ω d q O) (V : Point d → ℝ)
    (hV : Measurable (firstOrderReply V)) (n : ℕ) :
    Measurable (A.history V · n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    simp only [history]
    split_ifs with hn
    · apply Measurable.of_eval
      intro i
      by_cases hi : i = ⟨n,hn⟩
      · subst i
        simp only [Function.update_self]
        exact hV.comp ((A.query_measurable _).comp (measurable_id.prodMk ih))
      · simp only [Function.update_of_ne hi]
        exact (measurable_pi_apply i).comp ih
    · exact ih

lemma measurable_run (A : Program Ω d q O) (V : Point d → ℝ)
    (hV : Measurable (firstOrderReply V)) : Measurable (A.run V) :=
  A.output_measurable.comp (measurable_id.prodMk (A.measurable_history V hV q))

end Program
end LogConcaveSampling.OracleCompiler

namespace LogConcaveSampling.OracleCompiler.Program
variable {Ω O R : Type*} [MeasurableSpace Ω] [MeasurableSpace O] [MeasurableSpace R]
  {d q r : ℕ}

def leftTrace (h : Transcript d (q+r)) : Transcript d q := fun i => h (Fin.castAdd r i)
def rightTrace (h : Transcript d (q+r)) : Transcript d r := fun i => h (Fin.natAdd q i)

lemma measurable_leftTrace : Measurable (leftTrace (d:=d) (q:=q) (r:=r)) := by
  exact Measurable.of_eval fun index => measurable_pi_apply (Fin.castAdd r index)
lemma measurable_rightTrace : Measurable (rightTrace (d:=d) (q:=q) (r:=r)) := by
  exact Measurable.of_eval fun index => measurable_pi_apply (Fin.natAdd q index)

@[simp] lemma leftTrace_append (h : Transcript d q) (k : Transcript d r) :
    leftTrace (Fin.append h k) = h := by
  funext i
  simp [leftTrace]
@[simp] lemma rightTrace_append (h : Transcript d q) (k : Transcript d r) :
    rightTrace (Fin.append h k) = k := by
  funext i
  simp [rightTrace]

lemma leftTrace_prefix_left (h : Transcript d q) (k : Transcript d r) (n : ℕ) :
    leftTrace (mask n (Fin.append h k)) = mask n h := by
  funext i
  simp [leftTrace, mask]

lemma leftTrace_prefix_right (h : Transcript d q) (k : Transcript d r) (n : ℕ) :
    leftTrace (mask (q+n) (Fin.append h k)) = h := by
  funext i
  have hi : i.val < q+n := by omega
  simp [leftTrace, mask, hi]

lemma rightTrace_prefix_right (h : Transcript d q) (k : Transcript d r) (n : ℕ) :
    rightTrace (mask (q+n) (Fin.append h k)) = mask n k := by
  funext i
  simp [rightTrace, mask]

def seq (A : Program Ω d q O) (B : Program (Ω × O) d r R) :
    Program Ω d (q+r) R where
  query i p := Fin.addCases
    (fun j => A.query j (p.1, leftTrace p.2))
    (fun j => B.query j ((p.1, A.output (p.1,leftTrace p.2)), rightTrace p.2)) i
  query_measurable i := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.addCases_left, Function.comp_def] using (A.query_measurable j).comp
        (measurable_fst.prodMk (measurable_leftTrace.comp measurable_snd))
    · simpa only [Fin.addCases_right, Function.comp_def] using (B.query_measurable j).comp
        ((measurable_fst.prodMk (A.output_measurable.comp
          (measurable_fst.prodMk (measurable_leftTrace.comp measurable_snd)))).prodMk
          (measurable_rightTrace.comp measurable_snd))
  output p := B.output ((p.1,A.output (p.1,leftTrace p.2)), rightTrace p.2)
  output_measurable := B.output_measurable.comp
    ((measurable_fst.prodMk (A.output_measurable.comp
      (measurable_fst.prodMk (measurable_leftTrace.comp measurable_snd)))).prodMk
        (measurable_rightTrace.comp measurable_snd))

lemma seq_history (A : Program Ω d q O) (B : Program (Ω × O) d r R)
    (V : Point d → ℝ) (ω : Ω) :
    (A.seq B).history V ω (q+r) =
      Fin.append (A.history V ω q) (B.history V (ω,A.run V ω) r) := by
  apply history_unique
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.append_left, seq, Fin.addCases_left, Fin.val_castAdd,
      leftTrace_prefix_left]
    exact A.history_spec V ω j
  · simp only [Fin.append_right, seq, Fin.addCases_right, Fin.val_natAdd,
      leftTrace_prefix_right, rightTrace_prefix_right]
    exact B.history_spec V (ω,A.run V ω) j

lemma seq_run (A : Program Ω d q O) (B : Program (Ω × O) d r R)
    (V : Point d → ℝ) (ω : Ω) :
    (A.seq B).run V ω = B.run V (ω,A.run V ω) := by
  unfold run
  rw [seq_history]
  simp only [seq, leftTrace_append, rightTrace_append]
  rfl

def map (A : Program Ω d q O) (f : Ω × O → R) (hf : Measurable f) : Program Ω d q R where
  query := A.query
  query_measurable := A.query_measurable
  output p := f (p.1,A.output p)
  output_measurable := hf.comp (measurable_fst.prodMk A.output_measurable)

lemma map_history (A : Program Ω d q O) (f : Ω × O → R) (hf : Measurable f)
    (V : Point d → ℝ) (ω : Ω) (n : ℕ) :
    (A.map f hf).history V ω n = A.history V ω n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [history, ih]
    rfl

lemma map_run (A : Program Ω d q O) (f : Ω × O → R) (hf : Measurable f)
    (V : Point d → ℝ) (ω : Ω) : (A.map f hf).run V ω = f (ω,A.run V ω) := by
  unfold run
  rw [map_history]
  rfl

def seedMap {Ξ : Type*} [MeasurableSpace Ξ] (A : Program Ω d q O)
    (f : Ξ → Ω) (hf : Measurable f) : Program Ξ d q O where
  query i p := A.query i (f p.1, p.2)
  query_measurable i := (A.query_measurable i).comp
    ((hf.comp measurable_fst).prodMk measurable_snd)
  output p := A.output (f p.1,p.2)
  output_measurable := A.output_measurable.comp
    ((hf.comp measurable_fst).prodMk measurable_snd)

lemma seedMap_history {Ξ : Type*} [MeasurableSpace Ξ] (A : Program Ω d q O)
    (f : Ξ → Ω) (hf : Measurable f) (V : Point d → ℝ) (ω : Ξ) (n : ℕ) :
    (A.seedMap f hf).history V ω n = A.history V (f ω) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [history, ih]
    rfl

lemma seedMap_run {Ξ : Type*} [MeasurableSpace Ξ] (A : Program Ω d q O)
    (f : Ξ → Ω) (hf : Measurable f) (V : Point d → ℝ) (ω : Ξ) :
    (A.seedMap f hf).run V ω = A.run V (f ω) := by
  unfold run
  rw [seedMap_history]
  rfl

def pure (f : Ω → O) (hf : Measurable f) : Program Ω d 0 O where
  query i := Fin.elim0 i
  query_measurable i := Fin.elim0 i
  output p := f p.1
  output_measurable := hf.comp measurable_fst

@[simp] lemma pure_run (f : Ω → O) (hf : Measurable f) (V : Point d → ℝ) (ω : Ω) :
    (pure (d:=d) f hf).run V ω = f ω := rfl

def oneQuery (x : Ω → Point d) (hx : Measurable x)
    (f : Ω × Reply d → O) (hf : Measurable f) : Program Ω d 1 O where
  query _ p := x p.1
  query_measurable _ := hx.comp measurable_fst
  output p := f (p.1,p.2 0)
  output_measurable := hf.comp (measurable_fst.prodMk
    ((measurable_pi_apply 0).comp measurable_snd))

lemma oneQuery_run (x : Ω → Point d) (hx : Measurable x)
    (f : Ω × Reply d → O) (hf : Measurable f) (V : Point d → ℝ) (ω : Ω) :
    (oneQuery x hx f hf).run V ω = f (ω, firstOrderReply V (x ω)) := by
  simp [run, history, oneQuery]

end LogConcaveSampling.OracleCompiler.Program

namespace LogConcaveSampling.OracleCompiler.Program
variable {Ω O : Type*} [MeasurableSpace Ω] [MeasurableSpace O] {d q r : ℕ}

def castCap (h : q = r) (A : Program Ω d q O) : Program Ω d r O := h ▸ A

lemma castCap_run (h : q = r) (A : Program Ω d q O) (V : Point d → ℝ) (ω : Ω) :
    (A.castCap h).run V ω = A.run V ω := by subst r; rfl

def iterate (A : Program (Ω × O) d q O) (init : Ω → O) (hi : Measurable init) :
    (n : ℕ) → Program Ω d (n*q) O
  | 0 => (pure init hi).castCap (Nat.zero_mul q).symm
  | n+1 => ((iterate A init hi n).seq A).castCap (Nat.succ_mul n q).symm

lemma iterate_run (A : Program (Ω × O) d q O) (init : Ω → O) (hi : Measurable init)
    (V : Point d → ℝ) (ω : Ω) (n : ℕ) :
    (A.iterate init hi n).run V ω = (fun x => A.run V (ω,x))^[n] (init ω) := by
  induction n with
  | zero => simp only [iterate, castCap_run, pure_run, Function.iterate_zero_apply]
  | succ n ih =>
    rw [iterate, castCap_run, seq_run, ih]
    exact (Function.iterate_succ_apply' (fun x => A.run V (ω,x)) n (init ω)).symm

end LogConcaveSampling.OracleCompiler.Program

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace LogConcaveSampling.SeedCompiler

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def slotSum (a : ι → ℝ) (g : ι → E) : E := ∑ i, a i • g i

def slotTransform (c : ℝ) (a : ι → ℝ) (g : ι → E) : ι → E :=
  fun i => g i - (c * a i) • slotSum a g

omit [DecidableEq ι] in
lemma slot_energy (c : ℝ) (a : ι → ℝ)
    (hc : c ^ 2 * (∑ i, a i ^ 2) - 2 * c + 1 = 0) (g : ι → E) :
    (∑ i, ‖slotTransform c a g i‖ ^ 2) + ‖slotSum a g‖ ^ 2 =
      ∑ i, ‖g i‖ ^ 2 := by
  let S := slotSum a g
  have hi : ∑ i, a i * inner ℝ (g i) S = ‖S‖ ^ 2 := by
    simp_rw [← real_inner_smul_left]
    rw [← sum_inner]
    exact real_inner_self_eq_norm_sq S
  have hsum : (∑ i, ‖slotTransform c a g i‖ ^ 2) =
      (∑ i, ‖g i‖ ^ 2) - (2 * c) * (∑ i, a i * inner ℝ (g i) S) +
        c ^ 2 * (∑ i, a i ^ 2) * ‖S‖ ^ 2 := by
    simp only [slotTransform, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs, real_inner_smul_right]
    dsimp only [S]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp only [Finset.mul_sum, Finset.sum_mul]
    simp only [mul_assoc, mul_comm, mul_left_comm]
  rw [hsum, hi]
  change _ + ‖S‖ ^ 2 = _
  nlinarith [mul_eq_zero_of_left hc (‖S‖ ^ 2)]

def restored (c : ℝ) (a : ι → ℝ) : ((ι → E) × E) →L[ℝ] (ι → E) :=
  ContinuousLinearMap.pi fun i =>
    ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ (ι → E) E)) -
    (c * a i) • (∑ j, a j •
      ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.fst ℝ (ι → E) E))) -
    a i • ContinuousLinearMap.snd ℝ (ι → E) E

omit [DecidableEq ι] in
@[simp] lemma restored_apply (c : ℝ) (a : ι → ℝ) (g : ι → E) (z : E) (i : ι) :
    restored c a (g,z) i = slotTransform c a g i - a i • z := by
  simp [restored, slotTransform, slotSum]

lemma dual_restored_left (c : ℝ) (a : ι → ℝ) (L : StrongDual ℝ (ι → E)) (j : ι) :
    ((L.comp (restored c a)).comp (ContinuousLinearMap.inl ℝ (ι → E) E)).comp
        (ContinuousLinearMap.single ℝ (fun _ : ι => E) j) =
      L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => E) j) -
        (c * a j) • ∑ i, a i • L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => E) i) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.single_apply]
  have h : restored c a (Pi.single j x,0) =
      Pi.single j x - (c * a j) • ∑ i, a i • Pi.single i x := by
    ext k
    simp [slotTransform, slotSum, Pi.single_apply, smul_smul, mul_comm, mul_left_comm]
  rw [h, map_sub, map_smul, map_sum]
  simp

lemma dual_restored_right (c : ℝ) (a : ι → ℝ) (L : StrongDual ℝ (ι → E)) :
    (L.comp (restored c a)).comp (ContinuousLinearMap.inr ℝ (ι → E) E) =
      -(∑ i, a i • L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => E) i)) := by
  ext x
  have h : restored c a (0,x) = -(∑ i, a i • Pi.single i x) := by
    ext k
    simp [slotTransform, slotSum, Pi.single_apply]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  rw [h, map_neg, map_sum]
  simp

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem restored_gaussian (c : ℝ) (a : ι → ℝ)
    (hc : c ^ 2 * (∑ i, a i ^ 2) - 2 * c + 1 = 0) :
    ((Measure.pi (fun _ : ι => stdGaussian E)).prod (stdGaussian E)).map
      (restored c a) = Measure.pi (fun _ : ι => stdGaussian E) := by
  apply Measure.ext_of_charFunDual
  ext L
  rw [charFunDual_map, charFunDual_prod, charFunDual_pi, charFunDual_pi]
  simp_rw [dual_restored_left, dual_restored_right, charFunDual_stdGaussian,
    ← Complex.exp_sum, ← Complex.exp_add]
  congr 1
  let D := InnerProductSpace.toDual ℝ E
  let l := fun i => L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => E) i)
  have he := slot_energy c a hc (fun i => D.symm (l i))
  simp only [slotTransform, slotSum, ← map_smul, ← map_sum, ← map_sub,
    LinearIsometryEquiv.norm_map] at he
  simp only [norm_neg]
  norm_cast
  dsimp only [l] at he
  simp only [← Finset.sum_div, Finset.sum_neg_distrib]
  linarith

def sqrtCoefficient (a : ι → ℝ) : ℝ := 1 / (1 + Real.sqrt (1 - ∑ i, a i ^ 2))

omit [DecidableEq ι] in
lemma sqrtCoefficient_equation (a : ι → ℝ) (ha : (∑ i, a i ^ 2) ≤ 1) :
    (sqrtCoefficient a) ^ 2 * (∑ i, a i ^ 2) - 2 * sqrtCoefficient a + 1 = 0 := by
  have hsq := Real.sq_sqrt (sub_nonneg.mpr ha)
  have hpos : 0 < 1 + Real.sqrt (1 - ∑ i, a i ^ 2) := by positivity
  unfold sqrtCoefficient
  field_simp
  nlinarith

theorem sqrt_restored_gaussian (a : ι → ℝ) (ha : (∑ i, a i ^ 2) ≤ 1) :
    ((Measure.pi (fun _ : ι => stdGaussian E)).prod (stdGaussian E)).map
      (restored (sqrtCoefficient a) a) = Measure.pi (fun _ : ι => stdGaussian E) :=
  restored_gaussian _ _ (sqrtCoefficient_equation a ha)

end LogConcaveSampling.SeedCompiler

namespace LogConcaveSampling.SeedCompiler
variable {ι E O : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def ShiftInvariant (r : ℝ) (v : ι → ℝ) (M : E → (ι → E) → O) : Prop :=
  ∀ x Δ g, M (x + r • Δ) (fun i => g i + v i • Δ) = M x g

omit [DecidableEq ι] in
lemma absorption_pathwise {r D : ℝ} (v : ι → ℝ)
    (M : E → (ι → E) → O) (hM : ShiftInvariant r v M)
    (x : E) (c : ℝ) (g : ι → E) (z : E) :
    M (x + (r / (2 * D)) • z)
        (slotTransform c (fun i => v i / (2 * D)) g) =
      M x (restored c (fun i => v i / (2 * D)) (g,z)) := by
  have h := hM x ((1 / (2 * D)) • z)
    (restored c (fun i => v i / (2 * D)) (g,z))
  have hx : r • ((1 / (2 * D)) • z) = (r / (2 * D)) • z := by
    rw [smul_smul]; congr 1; ring
  have hs : (fun i => restored c (fun i => v i / (2 * D)) (g,z) i +
      v i • ((1 / (2 * D)) • z)) = slotTransform c (fun i => v i / (2 * D)) g := by
    funext i
    simp only [restored_apply, smul_smul]
    have hc : v i * (1 / (2 * D)) = v i / (2 * D) := by ring
    rw [hc, sub_add_cancel]
  simpa only [hx, hs] using h

omit [DecidableEq ι] in
lemma normalized_shift_bound {D : ℝ} (hD : 0 < D) (v : ι → ℝ)
    (hv : (∑ i, v i ^ 2) ≤ D ^ 2) :
    (∑ i, (v i / (2 * D)) ^ 2) ≤ 1 / 4 := by
  simp only [div_pow, ← Finset.sum_div]
  apply (div_le_iff₀ (sq_pos_of_pos (mul_pos (by norm_num) hD))).mpr
  nlinarith

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace O]

theorem absorption_law {r D : ℝ} (hD : 0 < D) (v : ι → ℝ)
    (hv : (∑ i, v i ^ 2) ≤ D ^ 2) (M : E → (ι → E) → O)
    (hshift : ShiftInvariant r v M) (x : E) (hm : Measurable (M x)) :
    let a := fun i => v i / (2 * D)
    ((Measure.pi (fun _ : ι => stdGaussian E)).prod (stdGaussian E)).map
      (fun p => M (x + (r / (2 * D)) • p.2) (slotTransform (sqrtCoefficient a) a p.1)) =
      (Measure.pi (fun _ : ι => stdGaussian E)).map (M x) := by
  dsimp only
  let a := fun i => v i / (2 * D)
  have ha : (∑ i, a i ^ 2) ≤ 1 := (normalized_shift_bound hD v hv).trans (by norm_num)
  have he : (fun p : (ι → E) × E =>
      M (x + (r / (2 * D)) • p.2) (slotTransform (sqrtCoefficient a) a p.1)) =
      (M x) ∘ restored (sqrtCoefficient a) a := by
    funext p
    exact absorption_pathwise v M hshift x _ p.1 p.2
  rw [he, ← Measure.map_map hm (by fun_prop), sqrt_restored_gaussian a ha]

theorem restored_with_anchors {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [SFinite μ] (a : ι → ℝ) (ha : (∑ i, a i ^ 2) ≤ 1) :
    (μ.prod ((Measure.pi (fun _ : ι => stdGaussian E)).prod (stdGaussian E))).map
      (Prod.map id (restored (sqrtCoefficient a) a)) =
      μ.prod (Measure.pi (fun _ : ι => stdGaussian E)) := by
  rw [← Measure.map_prod_map μ _ measurable_id (by fun_prop), Measure.map_id,
    sqrt_restored_gaussian a ha]

theorem absorption_with_anchors {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [SFinite μ] {r D : ℝ} (hD : 0 < D) (v : ι → ℝ)
    (hv : (∑ i, v i ^ 2) ≤ D ^ 2) (M : E → (ι → E) → O)
    (hshift : ShiftInvariant r v M) (hm : Measurable (Function.uncurry M))
    (x : A → E) (hx : Measurable x) :
    let a := fun i => v i / (2 * D)
    (μ.prod ((Measure.pi (fun _ : ι => stdGaussian E)).prod (stdGaussian E))).map
      (fun p => (p.1, M (x p.1 + (r / (2 * D)) • p.2.2)
        (slotTransform (sqrtCoefficient a) a p.2.1))) =
      (μ.prod (Measure.pi (fun _ : ι => stdGaussian E))).map
        (fun p => (p.1, M (x p.1) p.2)) := by
  dsimp only
  let a := fun i => v i / (2 * D)
  have ha : (∑ i, a i ^ 2) ≤ 1 := (normalized_shift_bound hD v hv).trans (by norm_num)
  have hf : Measurable (fun p : A × (ι → E) => (p.1, M (x p.1) p.2)) :=
    measurable_fst.prodMk (hm.comp ((hx.comp measurable_fst).prodMk measurable_snd))
  rw [← restored_with_anchors μ a ha, Measure.map_map hf (by fun_prop)]
  congr 1
  funext p
  congr 1
  exact absorption_pathwise v M hshift (x p.1) _ p.2.1 p.2.2

end LogConcaveSampling.SeedCompiler

namespace LogConcaveSampling.SeedCompiler
variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma slotSum_transform (c : ℝ) (a : ι → ℝ) (g : ι → E) :
    slotSum a (slotTransform c a g) = (1 - c * ∑ i, a i ^ 2) • slotSum a g := by
  simp only [slotSum, slotTransform, smul_sub, smul_smul, Finset.sum_sub_distrib,
    ← Finset.sum_smul, sub_smul, one_smul]
  congr 2
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma slotTransform_comp (c t : ℝ) (a : ι → ℝ) (g : ι → E) :
    slotTransform t a (slotTransform c a g) =
      slotTransform (c + t - t * c * ∑ i, a i ^ 2) a g := by
  funext i
  simp only [slotTransform, slotSum_transform, smul_smul]
  rw [sub_sub, ← add_smul]
  congr 2
  ring

lemma slotTransform_square (a : ι → ℝ) (ha : (∑ i, a i ^ 2) ≤ 1) (g : ι → E) :
    slotTransform (sqrtCoefficient a) a (slotTransform (sqrtCoefficient a) a g) =
      fun i => g i - a i • slotSum a g := by
  rw [slotTransform_comp]
  have h : sqrtCoefficient a + sqrtCoefficient a -
      sqrtCoefficient a * sqrtCoefficient a * ∑ i, a i ^ 2 = 1 := by
    nlinarith [sqrtCoefficient_equation a ha]
  rw [h]
  funext i
  simp [slotTransform]

lemma slotSum_energy_bound (a : ι → ℝ) (g : ι → E) :
    ‖slotSum a g‖ ^ 2 ≤ (∑ i, a i ^ 2) * (∑ i, ‖g i‖ ^ 2) := by
  calc
    ‖slotSum a g‖ ^ 2 ≤ (∑ i, |a i| * ‖g i‖) ^ 2 := by
      apply sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun i _ => by positivity) |>.mpr
      simpa [slotSum, norm_smul] using norm_sum_le Finset.univ (fun i => a i • g i)
    _ ≤ (∑ i, |a i| ^ 2) * (∑ i, ‖g i‖ ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => |a i|) (fun i => ‖g i‖)
    _ = _ := by simp only [sq_abs]

lemma sqrtCoefficient_nonneg (a : ι → ℝ) : 0 ≤ sqrtCoefficient a := by
  unfold sqrtCoefficient
  positivity

lemma sqrtCoefficient_le_one (a : ι → ℝ) : sqrtCoefficient a ≤ 1 := by
  unfold sqrtCoefficient
  rw [div_le_iff₀ (by positivity : 0 < 1 + Real.sqrt (1 - ∑ i, a i ^ 2))]
  nlinarith [Real.sqrt_nonneg (1 - ∑ i, a i ^ 2)]

lemma slotTransform_positive (a : ι → ℝ) (ha : (∑ i, a i ^ 2) ≤ 1) (g : ι → E) :
    0 ≤ ∑ i, inner ℝ (g i) (slotTransform (sqrtCoefficient a) a g i) := by
  have hs : ∑ i, a i * inner ℝ (g i) (slotSum a g) = ‖slotSum a g‖ ^ 2 := by
    simp_rw [← real_inner_smul_left]
    rw [← sum_inner]
    exact real_inner_self_eq_norm_sq _
  have hb := slotSum_energy_bound a g
  have hc := sqrtCoefficient_nonneg a
  have hc' := sqrtCoefficient_le_one a
  have hA : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hG : 0 ≤ ∑ i, ‖g i‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hAG : (∑ i, a i ^ 2) * (∑ i, ‖g i‖ ^ 2) ≤ ∑ i, ‖g i‖ ^ 2 := by
    nlinarith
  simp only [slotTransform, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  rw [hs]
  nlinarith [sq_nonneg ‖slotSum a g‖]

lemma sqrtCoefficient_eigenvalue (a : ι → ℝ) (ha : (∑ i, a i ^ 2) ≤ 1) :
    1 - sqrtCoefficient a * ∑ i, a i ^ 2 = Real.sqrt (1 - ∑ i, a i ^ 2) := by
  have hs := Real.sq_sqrt (sub_nonneg.mpr ha)
  have hp : 0 < 1 + Real.sqrt (1 - ∑ i, a i ^ 2) := by positivity
  unfold sqrtCoefficient
  field_simp
  nlinarith

def inverseCoefficient (a : ι → ℝ) : ℝ :=
  -sqrtCoefficient a / Real.sqrt (1 - ∑ i, a i ^ 2)

lemma inverseCoefficient_cancel (a : ι → ℝ) (ha : (∑ i, a i ^ 2) < 1) :
    sqrtCoefficient a + inverseCoefficient a -
      inverseCoefficient a * sqrtCoefficient a * ∑ i, a i ^ 2 = 0 := by
  have he := sqrtCoefficient_eigenvalue a ha.le
  have hp : 0 < Real.sqrt (1 - ∑ i, a i ^ 2) := Real.sqrt_pos.mpr (sub_pos.mpr ha)
  unfold inverseCoefficient
  field_simp
  rw [← he]
  ring

lemma inverse_slotTransform (a : ι → ℝ) (ha : (∑ i, a i ^ 2) < 1) (g : ι → E) :
    slotTransform (inverseCoefficient a) a (slotTransform (sqrtCoefficient a) a g) = g := by
  rw [slotTransform_comp, inverseCoefficient_cancel a ha]
  funext i
  simp [slotTransform]

lemma slotTransform_inverse (a : ι → ℝ) (ha : (∑ i, a i ^ 2) < 1) (g : ι → E) :
    slotTransform (sqrtCoefficient a) a (slotTransform (inverseCoefficient a) a g) = g := by
  rw [slotTransform_comp]
  have he := inverseCoefficient_cancel a ha
  have : inverseCoefficient a + sqrtCoefficient a -
      sqrtCoefficient a * inverseCoefficient a * ∑ i, a i ^ 2 = 0 := by nlinarith
  rw [this]
  funext i
  simp [slotTransform]

lemma inverse_slot_energy (a : ι → ℝ) (ha : (∑ i, a i ^ 2) ≤ 1 / 4) (g : ι → E) :
    (∑ i, ‖slotTransform (inverseCoefficient a) a g i‖ ^ 2) ≤
      4 * ∑ i, ‖g i‖ ^ 2 := by
  let h := slotTransform (inverseCoefficient a) a g
  have hA : (∑ i, a i ^ 2) < 1 := ha.trans_lt (by norm_num)
  have he := slot_energy (sqrtCoefficient a) a (sqrtCoefficient_equation a hA.le) h
  rw [slotTransform_inverse a hA g] at he
  have hb := slotSum_energy_bound a h
  have hs : 0 ≤ ∑ i, ‖h i‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB : (∑ i, a i ^ 2) * (∑ i, ‖h i‖ ^ 2) ≤ (1 / 4) * (∑ i, ‖h i‖ ^ 2) :=
    mul_le_mul_of_nonneg_right ha hs
  change (∑ i, ‖h i‖ ^ 2) ≤ _
  nlinarith

end LogConcaveSampling.SeedCompiler

end
end
end
end

end OAI
