import OAI.Combinatorics.ParityLifts.FunctionalCode

namespace OAI

namespace ParityWL.Complexity

lemma FWhile.lower {S r : ℕ} {f : FCode} (i j : Fin r) (hj : j.val = i.val + 1)
    (hf : i.val + f.depth ≤ r)
    (realize : ∀ {x y n}, FEval S f x n y → ∀ (d : Fin r → DataTree),
      d i = x → CleanAbove d i → DataBound d (2 * S + 1) →
      ∃ m, m ≤ f.factor * n ∧
        BCodeExec (2 * S + 1) (f.lower i hf) d m (Function.update d i y))
    {x y n} (h : FWhile S (FEval S f) x n y) (d : Fin r → DataTree)
    (hdi : d i = x) (hc : CleanAbove d i) (hd : DataBound d (2 * S + 1)) :
    ∃ m, m ≤ (f.factor + 10) * n ∧
      BCodeExec (2 * S + 1)
        (.loop j (.seq (.op (.nil j)) (.seq (f.lower i hf) (.op (.project j i false)))))
        (Function.update d j (x.child false)) m (Function.update d i y) := by
  have hji : j ≠ i := by intro he; subst j; omega
  have hnil : d j = .nil := hc j (by omega)
  induction h generalizing d with
  | stop x hx he =>
    have h₁ : Function.update d j (x.child false) = d := by rw [he, ← hnil]; exact Function.update_eq_self j d
    have h₂ : Function.update d i x = d := by rw [← hdi]; exact Function.update_eq_self i d
    refine ⟨1, by omega, ?_⟩
    rw [h₁, h₂]
    exact .nil_loop hnil hd
  | @next x y z n m he hb ht ih =>
    let a := Function.update d j (x.child false)
    have ha : DataBound a (2 * S + 1) := hd.update j _
      ((x.size_child false).trans (by have := hb.bounds.1; omega))
    have h₁ : BCodeExec (2 * S + 1) (.op (.nil j)) a 2 d := by
      simpa [a, ← hnil] using BCodeExec.nil j a ha
    obtain ⟨u, hu, hfRun⟩ := realize hb d hdi hc hd
    have hc' : CleanAbove (Function.update d i y) i := hc.update_self y
    have h₃ := BCodeExec.project j i false _ hfRun.end_bound
    have hh : BCodeExec (2 * S + 1)
        (.seq (.op (.nil j)) (.seq (f.lower i hf) (.op (.project j i false))))
        a (u + 6) (Function.update (Function.update d i y) j (y.child false)) := by
      convert h₁.seq (hfRun.seq h₃) using 1 <;> simp
      omega
    obtain ⟨v, hv, hl⟩ := ih (Function.update d i y) (by simp) hc' hfRun.end_bound
      (by simp [hji, hnil])
    have hres := BCodeExec.node_loop (i := j) (by simpa [a] using he) hh hl
    refine ⟨u + 6 + v + 3, ?_, ?_⟩
    · nlinarith
    · simpa using hres

lemma FEval.lower {S : ℕ} {f : FCode} {x y : DataTree} {n : ℕ}
    (h : FEval S f x n y) {r : ℕ} (i : Fin r) (hi : i.val + f.depth ≤ r)
    (d : Fin r → DataTree) (hdi : d i = x) (hc : CleanAbove d i)
    (hd : DataBound d (2 * S + 1)) :
    ∃ m, m ≤ f.factor * n ∧
      BCodeExec (2 * S + 1) (f.lower i hi) d m (Function.update d i y) := by
  induction f generalizing r i S d x y n with
  | id =>
    cases h with
    | id x hx =>
      refine ⟨0, by simp, ?_⟩
      simpa [FCode.lower, ← hdi] using BCodeExec.skip d hd
  | nil =>
    cases h with
    | nil x hx => exact ⟨2, by simp [FCode.factor], BCodeExec.nil i d hd⟩
  | left =>
    cases h with
    | left x hx =>
      refine ⟨2, by simp [FCode.factor], ?_⟩
      simpa [FCode.lower, hdi] using BCodeExec.project i i false d hd
  | right =>
    cases h with
    | right x hx =>
      refine ⟨2, by simp [FCode.factor], ?_⟩
      simpa [FCode.lower, hdi] using BCodeExec.project i i true d hd
  | pair f g ihf ihg =>
    cases h with
    | @pair _ _ _ y z n m hhf hhg hsz =>
      have hjr : i.val + 1 < r := by have := g.depth_pos; simp only [FCode.depth] at hi; omega
      have hkr : i.val + 2 < r := by have := g.depth_pos; simp only [FCode.depth] at hi; omega
      let j : Fin r := ⟨i.val + 1, hjr⟩
      let k : Fin r := ⟨i.val + 2, hkr⟩
      have hji : j ≠ i := by intro hh; have := congrArg Fin.val hh; dsimp [j] at this; omega
      have hki : k ≠ i := by intro hh; have := congrArg Fin.val hh; dsimp [k] at this; omega
      have hkj : k ≠ j := by intro hh; have := congrArg Fin.val hh; dsimp [j, k] at this; omega
      have hnj : d j = .nil := hc j (by dsimp [j]; omega)
      have hnk : d k = .nil := hc k (by dsimp [k]; omega)
      let d₁ := Function.update d j x
      have h₁ : BCodeExec (2 * S + 1) (.copy j i) d 5 d₁ := by
        simpa [d₁, hdi] using BCodeExec.copy j i d hd (hdi ▸ hhf.bounds.1)
      have hc₁ : CleanAbove d₁ j := hc.update_later (by dsimp [j]; omega) x
      have hfj : j.val + f.depth ≤ r := by dsimp [j]; simp only [FCode.depth] at hi; omega
      obtain ⟨a, ha, h₂⟩ := ihf hhf j hfj d₁ (by simp [d₁]) hc₁ h₁.end_bound
      let d₂ := Function.update d j y
      have h₂' : BCodeExec (2 * S + 1) (f.lower j hfj) d₁ a d₂ := by
        simpa [d₁, d₂] using h₂
      let d₃ := Function.update d₂ k x
      have h₃ : BCodeExec (2 * S + 1) (.copy k i) d₂ 5 d₃ := by
        have hd₂i : d₂ i = x := by simp [d₂, Ne.symm hji, hdi]
        simpa [d₃, hd₂i] using BCodeExec.copy k i d₂ h₂'.end_bound (hd₂i ▸ hhg.bounds.1)
      have hc₂ : CleanAbove d₂ j := hc.update_later (by dsimp [j]; omega) y
      have hc₃ : CleanAbove d₃ k := hc₂.update_later (by dsimp [j, k]; omega) x
      have hgk : k.val + g.depth ≤ r := by dsimp [k]; simp only [FCode.depth] at hi; omega
      obtain ⟨b, hb, h₄⟩ := ihg hhg k hgk d₃ (by simp [d₃]) hc₃ h₃.end_bound
      let d₄ := Function.update d₂ k z
      have h₄' : BCodeExec (2 * S + 1) (g.lower k hgk) d₃ b d₄ := by
        simpa [d₃, d₄] using h₄
      have h₅ := BCodeExec.node i j k d₄ h₄'.end_bound
        (by simpa [d₄, d₂, Ne.symm hkj] using (show (DataTree.node y z).size ≤ 2 * S + 1 by omega))
      have h₆ := BCodeExec.nil j _ h₅.end_bound
      have h₇ := BCodeExec.nil k _ h₆.end_bound
      have hres := h₁.seq (h₂'.seq (h₃.seq (h₄'.seq (h₅.seq (h₆.seq h₇)))))
      have he : Function.update (Function.update (Function.update d₄ i (.node (d₄ j) (d₄ k))) j .nil) k .nil =
          Function.update d i (.node y z) := by
        funext q
        by_cases hqk : q = k
        · subst q; simp [hki, hnk]
        by_cases hqj : q = j
        · subst q; simp [Ne.symm hkj, hji, hnj]
        by_cases hqi : q = i
        · subst q; simp [d₄, d₂, Ne.symm hji, Ne.symm hki, Ne.symm hkj]
        · simp [d₄, d₂, hqk, hqj, hqi]
      rw [he] at hres
      refine ⟨a + b + 22, ?_, ?_⟩
      · simp only [FCode.factor]; nlinarith
      · convert hres using 1 <;> first | rfl | omega
  | seq f g ihf ihg =>
    cases h with
    | seq hf hg =>
      have hfi : i.val + f.depth ≤ r := by simp only [FCode.depth] at hi; omega
      have hgi : i.val + g.depth ≤ r := by simp only [FCode.depth] at hi; omega
      obtain ⟨a, ha, h₁⟩ := ihf hf i hfi d hdi hc hd
      obtain ⟨b, hb, h₂⟩ := ihg hg i hgi _ (by simp) (hc.update_self _) h₁.end_bound
      refine ⟨a + 1 + b, ?_, ?_⟩
      · simp only [FCode.factor]; nlinarith
      · simpa [FCode.lower] using h₁.seq h₂
  | branch f g ihf ihg =>
    have hfi : i.val + f.depth ≤ r := by simp only [FCode.depth] at hi; omega
    have hgi : i.val + g.depth ≤ r := by simp only [FCode.depth] at hi; omega
    cases h with
    | nil_branch hf =>
      obtain ⟨a, ha, h₁⟩ := ihf hf i hfi d hdi hc hd
      exact ⟨a + 1, by simp only [FCode.factor]; nlinarith, h₁.nil_cond hdi⟩
    | node_branch hx hg =>
      obtain ⟨b, hb, h₂⟩ := ihg hg i hgi d hdi hc hd
      exact ⟨b + 1, by simp only [FCode.factor]; nlinarith, h₂.node_cond (by simpa [hdi] using hx)⟩
  | cond p f g ihp ihf ihg =>
    have hjr : i.val + 1 < r := by have := p.depth_pos; simp only [FCode.depth] at hi; omega
    let j : Fin r := ⟨i.val + 1, hjr⟩
    have hji : j ≠ i := by intro hh; have := congrArg Fin.val hh; dsimp [j] at this; omega
    have hnj : d j = .nil := hc j (by dsimp [j]; omega)
    have hpj : j.val + p.depth ≤ r := by dsimp [j]; simp only [FCode.depth] at hi; omega
    have hfi : i.val + f.depth ≤ r := by simp only [FCode.depth] at hi; omega
    have hgi : i.val + g.depth ≤ r := by simp only [FCode.depth] at hi; omega
    cases h with
    | nil_cond hp hf =>
      have h₁ : BCodeExec (2 * S + 1) (.copy j i) d 5 (Function.update d j x) := by
        simpa [hdi] using BCodeExec.copy j i d hd (hdi ▸ hp.bounds.1)
      obtain ⟨a, ha, h₂⟩ := ihp hp j hpj _ (by simp)
        (hc.update_later (by dsimp [j]; omega) x) h₁.end_bound
      have h₂' : BCodeExec (2 * S + 1) (p.lower j hpj) (Function.update d j x) a d := by
        simpa [← hnj] using h₂
      have h₃ : BCodeExec (2 * S + 1) (.op (.nil j)) d 2 d := by
        simpa [← hnj] using BCodeExec.nil j d hd
      obtain ⟨b, hb, h₄⟩ := ihf hf i hfi d hdi hc hd
      have hres := h₁.seq (h₂'.seq ((h₃.seq h₄).nil_cond (q := .seq (.op (.nil j)) (g.lower i hgi)) hnj))
      refine ⟨a + b + 11, ?_, ?_⟩
      · simp only [FCode.factor]; nlinarith
      · convert hres using 1 <;> first | rfl | omega
    | @node_cond _ _ _ _ _ z n m hp hz hg =>
      have h₁ : BCodeExec (2 * S + 1) (.copy j i) d 5 (Function.update d j x) := by
        simpa [hdi] using BCodeExec.copy j i d hd (hdi ▸ hp.bounds.1)
      obtain ⟨a, ha, h₂⟩ := ihp hp j hpj _ (by simp)
        (hc.update_later (by dsimp [j]; omega) x) h₁.end_bound
      have h₂' : BCodeExec (2 * S + 1) (p.lower j hpj) (Function.update d j x) a
          (Function.update d j z) := by simpa using h₂
      have h₃ : BCodeExec (2 * S + 1) (.op (.nil j)) (Function.update d j z) 2 d := by
        simpa [← hnj] using BCodeExec.nil j _ h₂'.end_bound
      obtain ⟨b, hb, h₄⟩ := ihg hg i hgi d hdi hc hd
      have hres := h₁.seq (h₂'.seq ((h₃.seq h₄).node_cond (i := j)
        (p := .seq (.op (.nil j)) (f.lower i hfi)) (by simpa using hz)))
      refine ⟨a + b + 11, ?_, ?_⟩
      · simp only [FCode.factor]; nlinarith
      · convert hres using 1 <;> first | rfl | omega
  | loop f ih =>
    have hfi : i.val + f.depth ≤ r := by simp only [FCode.depth] at hi; omega
    let j : Fin r := ⟨i.val + 1, by simp only [FCode.depth] at hi; omega⟩
    have hji : j ≠ i := by intro hh; have := congrArg Fin.val hh; dsimp [j] at this; omega
    have hnj : d j = .nil := hc j (by dsimp [j]; omega)
    obtain ⟨a, ha, hr⟩ := FWhile.lower i j rfl hfi (fun hh dd hdi hc hd => ih hh i hfi dd hdi hc hd)
      (FEval.loop_iff.mp h) d hdi hc hd
    have h₁ := BCodeExec.project j i false d hd
    simp only [hdi] at h₁
    have h₂ := BCodeExec.nil j _ hr.end_bound
    have he : Function.update (Function.update d i y) j .nil = Function.update d i y := by
      have hn : Function.update d i y j = .nil := by simp [hji, hnj]
      rw [← hn]
      exact Function.update_eq_self j _
    have hres := h₁.seq (hr.seq h₂)
    simp only [he] at hres
    refine ⟨a + 6, ?_, ?_⟩
    · have := h.bounds.2.2; simp only [FCode.factor]; nlinarith
    · convert hres using 1 <;> first | rfl | omega

end ParityWL.Complexity

namespace ParityWL.Complexity

noncomputable def FCode.decision (p : FCode) : Machine :=
  let i : Fin (p.depth + 1) := 0
  let P := (p.lower i (by simp [i])).compile.program
  (P.andThen (TreeMachine.branch i (.halt false) (.halt true))).compiled

lemma FEval.decision {S n : ℕ} {p : FCode} {bs : List Bool} {y : DataTree}
    (h : FEval S p (DataTree.ofBits bs) n y) :
    ∃ s, s ≤ 102 * (p.factor * n + 2) * ((p.depth + 1) * (2 * S + 1) + 1) +
      44 * bs.length + 20 ∧ Emits p.decision bs s (decide (y ≠ .nil)) := by
  let d := inputData p.depth bs
  let i : Fin (p.depth + 1) := 0
  have hdi : d i = DataTree.ofBits bs := by simp [d, i, inputData]
  have hd : DataBound d (2 * S + 1) := by
    intro j
    by_cases hj : j = 0
    · subst j; simp [d, inputData]; have := h.bounds.1; omega
    · simp [d, inputData, hj, DataTree.size]
  have hc : CleanAbove d i := by
    intro j hj
    have hn : j ≠ 0 := by intro hh; subst j; dsimp [i] at hj; omega
    simp [d, inputData, hn]
  obtain ⟨m, hm, hr⟩ := h.lower i (by simp [i]) d hdi hc hd
  let decider := TreeMachine.branch i (TreeMachine.halt (r := p.depth + 1) false) (.halt true)
  have he : BoundedRuns decider (2 * S + 1) (Function.update d i y) 1
      (Function.update d i y) (decide (y ≠ .nil)) := by
    by_cases hy : y = .nil
    · subst y
      simpa [decider] using (boundedHalt false _ hr.end_bound).branch_true i
        (.halt false) (.halt true) (by simp)
    · simpa [decider, hy] using (boundedHalt true _ hr.end_bound).branch_false i
        (.halt false) (.halt true) (by simpa using hy)
  have run := hr.compile.andThen he
  obtain ⟨s, hs, hem⟩ := run.compiled
  refine ⟨s, ?_, hem⟩
  have hmul : 102 * (m + 1 + 1) * ((p.depth + 1) * (2 * S + 1) + 1) ≤
      102 * (p.factor * n + 2) * ((p.depth + 1) * (2 * S + 1) + 1) := by
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
  omega

end ParityWL.Complexity

namespace ParityWL.Complexity

lemma FEval.mono {S T : ℕ} (hST : S ≤ T) {p : FCode} {x y : DataTree} {n : ℕ}
    (h : FEval S p x n y) : FEval T p x n y := by
  induction h with
  | id x hx => exact .id x (hx.trans hST)
  | nil x hx => exact .nil x (hx.trans hST)
  | left x hx => exact .left x (hx.trans hST)
  | right x hx => exact .right x (hx.trans hST)
  | pair _ _ hb hf hg => exact .pair hf hg (hb.trans hST)
  | seq _ _ hf hg => exact .seq hf hg
  | nil_branch _ hf => exact .nil_branch hf
  | node_branch hx _ hg => exact .node_branch hx hg
  | nil_cond _ _ hp hf => exact .nil_cond hp hf
  | node_cond _ hz _ hp hg => exact .node_cond hp hz hg
  | loop_stop f x hx he => exact .loop_stop f x (hx.trans hST) he
  | loop_next he _ _ hf ht => exact .loop_next he hf ht

/-- One common budget bounds both the number of functional instructions and
every intermediate serialized value. The compiler uses a universal quadratic
power, independent of the finite program's syntax. -/
def BEval (p : FCode) (x : DataTree) (B : ℕ) (y : DataTree) : Prop :=
  ∃ n, n ≤ B ∧ FEval B p x n y

lemma BEval.mono {p : FCode} {x y : DataTree} {B C : ℕ} (hBC : B ≤ C)
    (h : BEval p x B y) : BEval p x C y := by
  obtain ⟨n, hn, he⟩ := h
  exact ⟨n, hn.trans hBC, he.mono hBC⟩

lemma BEval.bounds {p : FCode} {x y : DataTree} {B : ℕ} (h : BEval p x B y) :
    x.size ≤ B ∧ y.size ≤ B ∧ 0 < B := by
  obtain ⟨n, hn, he⟩ := h
  have hh := he.bounds
  exact ⟨hh.1, hh.2.1, by omega⟩

lemma BEval.id (x : DataTree) : BEval .id x x.size x :=
  ⟨1, x.size_pos, .id x le_rfl⟩
lemma BEval.nil (x : DataTree) : BEval .nil x x.size .nil :=
  ⟨1, x.size_pos, .nil x le_rfl⟩
lemma BEval.left (x : DataTree) : BEval .left x x.size (x.child false) :=
  ⟨1, x.size_pos, .left x le_rfl⟩
lemma BEval.right (x : DataTree) : BEval .right x x.size (x.child true) :=
  ⟨1, x.size_pos, .right x le_rfl⟩

lemma BEval.pair {p q : FCode} {x y z : DataTree} {B C : ℕ}
    (h : BEval p x B y) (ht : BEval q x C z) : BEval (.pair p q) x (B + C + 1) (.node y z) := by
  obtain ⟨n, hn, he⟩ := h
  obtain ⟨m, hm, hf⟩ := ht
  refine ⟨n + m + 1, by omega, .pair (he.mono (by omega)) (hf.mono (by omega)) ?_⟩
  have := he.bounds.2.1
  have := hf.bounds.2.1
  simp only [DataTree.size]; omega

lemma BEval.seq {p q : FCode} {x y z : DataTree} {B C : ℕ}
    (h : BEval p x B y) (ht : BEval q y C z) : BEval (.seq p q) x (B + C + 1) z := by
  obtain ⟨n, hn, he⟩ := h
  obtain ⟨m, hm, hf⟩ := ht
  exact ⟨n + m + 1, by omega, .seq (he.mono (by omega)) (hf.mono (by omega))⟩

lemma BEval.nil_branch {p q : FCode} {y : DataTree} {B : ℕ}
    (h : BEval p .nil B y) : BEval (.branch p q) .nil (B + 1) y := by
  obtain ⟨n, hn, he⟩ := h
  exact ⟨n + 1, by omega, .nil_branch (he.mono (by omega))⟩

lemma BEval.node_branch {p q : FCode} {x y : DataTree} {B : ℕ}
    (hx : x ≠ .nil) (h : BEval q x B y) : BEval (.branch p q) x (B + 1) y := by
  obtain ⟨n, hn, he⟩ := h
  exact ⟨n + 1, by omega, .node_branch hx (he.mono (by omega))⟩

lemma BEval.nil_cond {p f g : FCode} {x y : DataTree} {B C : ℕ}
    (hp : BEval p x B .nil) (hf : BEval f x C y) : BEval (.cond p f g) x (B + C + 1) y := by
  obtain ⟨n, hn, he⟩ := hp
  obtain ⟨m, hm, ht⟩ := hf
  exact ⟨n + m + 1, by omega, .nil_cond (he.mono (by omega)) (ht.mono (by omega))⟩

lemma BEval.node_cond {p f g : FCode} {x y z : DataTree} {B C : ℕ}
    (hp : BEval p x B z) (hz : z ≠ .nil) (hg : BEval g x C y) :
    BEval (.cond p f g) x (B + C + 1) y := by
  obtain ⟨n, hn, he⟩ := hp
  obtain ⟨m, hm, ht⟩ := hg
  exact ⟨n + m + 1, by omega, .node_cond (he.mono (by omega)) hz (ht.mono (by omega))⟩

lemma BEval.loop_stop (p : FCode) (x : DataTree) (he : x.child false = .nil) :
    BEval (.loop p) x x.size x := ⟨1, x.size_pos, .loop_stop p x le_rfl he⟩

lemma BEval.loop_next {p : FCode} {x y z : DataTree} {B C : ℕ}
    (hx : x.child false ≠ .nil) (h : BEval p x B y) (ht : BEval (.loop p) y C z) :
    BEval (.loop p) x (B + C + 1) z := by
  obtain ⟨n, hn, he⟩ := h
  obtain ⟨m, hm, hf⟩ := ht
  exact ⟨n + m + 1, by omega, .loop_next hx (he.mono (by omega)) (hf.mono (by omega))⟩

lemma BEval.decision {p : FCode} {bs : List Bool} {y : DataTree} {B : ℕ}
    (h : BEval p (DataTree.ofBits bs) B y) :
    ∃ s, s ≤ 500 * (p.factor + 2) * (p.depth + 2) * (B + 1) ^ 2 +
      44 * bs.length + 20 ∧ Emits p.decision bs s (decide (y ≠ .nil)) := by
  obtain ⟨n, hn, he⟩ := h
  obtain ⟨s, hs, hr⟩ := he.decision
  refine ⟨s, hs.trans ?_, hr⟩
  have h₁ : p.factor * n + 2 ≤ (p.factor + 2) * (B + 1) := by nlinarith
  have h₂ : (p.depth + 1) * (2 * B + 1) + 1 ≤ 3 * (p.depth + 2) * (B + 1) := by nlinarith
  calc
    _ ≤ 102 * ((p.factor + 2) * (B + 1)) * (3 * (p.depth + 2) * (B + 1)) +
        44 * bs.length + 20 := by gcongr
    _ ≤ _ := by nlinarith [Nat.zero_le ((p.factor + 2) * (p.depth + 2) * (B + 1) ^ 2)]

end ParityWL.Complexity

end OAI
