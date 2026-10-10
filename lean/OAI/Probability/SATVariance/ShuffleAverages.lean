import OAI.Probability.SATVariance.HallSatisfiability

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

def listAvg.{u_1} {α : Type u_1} (l : List α) (f : α → ℝ) : ℝ :=
  (l.map f).sum / l.length

lemma listAvg_eq_favg.{u_1} {α : Type u_1} (l : List α) (f : α → ℝ) :
    listAvg l f = favg (fun i : Fin l.length => f (l.get i)) := by
  simp only [listAvg, favg, Fintype.card_fin]
  congr 1
  have he : List.ofFn (fun i : Fin l.length => f (l.get i)) = l.map f := by
    change List.ofFn (f ∘ l.get) = l.map f
    rw [← List.map_ofFn, List.ofFn_get]
  rw [← he]
  exact List.sum_ofFn

lemma listAvg_const.{u_1} {α : Type u_1} {l : List α} (hl : l ≠ []) (c : ℝ) :
    listAvg l (fun _ => c) = c := by
  rw [listAvg_eq_favg]
  have : Nonempty (Fin l.length) := Fin.pos_iff_nonempty.mp (List.length_pos_iff.mpr hl)
  exact favg_const c

lemma listAvg_congr.{u_1} {α : Type u_1} {l : List α} {f g : α → ℝ}
    (h : ∀ a ∈ l, f a = g a) : listAvg l f = listAvg l g := by
  unfold listAvg
  rw [List.map_congr_left h]

lemma listAvg_perm.{u_1} {α : Type u_1} {l r : List α} (h : l.Perm r) (f : α → ℝ) :
    listAvg l f = listAvg r f := by
  unfold listAvg
  rw [h.length_eq, (h.map f).sum_eq]

lemma listAvg_mono.{u_1} {α : Type u_1} {l : List α} {f g : α → ℝ}
    (h : ∀ a ∈ l, f a ≤ g a) : listAvg l f ≤ listAvg l g := by
  rw [listAvg_eq_favg, listAvg_eq_favg]
  exact favg_mono fun i => h _ (List.get_mem _ _)

lemma listAvg_nonneg.{u_1} {α : Type u_1} {l : List α} {f : α → ℝ}
    (h : ∀ a ∈ l, 0 ≤ f a) : 0 ≤ listAvg l f := by
  rw [listAvg_eq_favg]
  exact favg_nonneg fun i => h _ (List.get_mem _ _)

lemma listAvg_add.{u_1} {α : Type u_1} (l : List α) (f g : α → ℝ) :
    listAvg l (fun a => f a+g a) = listAvg l f+listAvg l g := by
  simp only [listAvg_eq_favg, favg_add]

lemma listAvg_sub.{u_1} {α : Type u_1} (l : List α) (f g : α → ℝ) :
    listAvg l (fun a => f a-g a) = listAvg l f-listAvg l g := by
  simp only [listAvg_eq_favg, favg_sub]

lemma listAvg_mul.{u_1} {α : Type u_1} (l : List α) (c : ℝ) (f : α → ℝ) :
    listAvg l (fun a => c*f a) = c*listAvg l f := by
  simp only [listAvg_eq_favg, favg_mul]

lemma listAvg_sq_le.{u_1} {α : Type u_1} {l : List α} (hl : l ≠ []) (f : α → ℝ) :
    (listAvg l f)^2 ≤ listAvg l (fun a => (f a)^2) := by
  simp only [listAvg_eq_favg]
  have : Nonempty (Fin l.length) := Fin.pos_iff_nonempty.mp (List.length_pos_iff.mpr hl)
  exact favg_sq_le _

lemma listAvg_flatMap.{u_1, u_2} {α : Type u_1} {β : Type u_2} (l : List α) (g : α → List β) (f : β → ℝ)
    (d : ℕ) (_hd : 0 < d) (h : ∀ a ∈ l, (g a).length = d) :
    listAvg (l.flatMap g) f = listAvg l (fun a => listAvg (g a) f) := by
  have hlen : (l.flatMap g).length = l.length*d := by
    rw [List.length_flatMap]
    calc
      _ = (l.map (fun _ => d)).sum := by congr 1; exact List.map_congr_left h
      _ = _ := by simp [List.sum_replicate, Nat.mul_comm]
  unfold listAvg
  have hsum (r : List α) : (r.flatMap (fun a => List.map f (g a))).sum =
      (r.map (fun a => (List.map f (g a)).sum)).sum := by
    induction r with
    | nil => simp
    | cons a r ih => simp [ih]
  rw [List.map_flatMap, hsum, hlen, Nat.cast_mul]
  have he : (l.map (fun a => (List.map f (g a)).sum / ((g a).length : ℝ))).sum =
      (l.map (fun a => (List.map f (g a)).sum)).sum / d := by
    calc
      _ = (l.map (fun a => (List.map f (g a)).sum / (d : ℝ))).sum := by
        congr 1
        exact List.map_congr_left (fun a ha => by rw [h a ha])
      _ = _ := by
        have hdiv (r : List α) : (r.map (fun a => (List.map f (g a)).sum / (d : ℝ))).sum =
            (r.map (fun a => (List.map f (g a)).sum)).sum / d := by
          induction r with
          | nil => simp
          | cons a r ih => simp [ih, add_div]
        exact hdiv l
  rw [he]
  ring

lemma permutations'_length.{u_1} {α : Type u_1} (l : List α) : l.permutations'.length = l.length.factorial := by
  rw [← (List.permutations_perm_permutations' l).length_eq, List.length_permutations]

lemma permutations'_ne_nil.{u_1} {α : Type u_1} (l : List α) : l.permutations' ≠ [] := by
  have hh : 0 < l.permutations'.length := by rw [permutations'_length]; exact Nat.factorial_pos _
  exact List.length_pos_iff.mp hh

def shuffleAvg.{u_1} {α : Type u_1} (l : List α) (f : List α → ℝ) : ℝ := listAvg l.permutations' f

lemma shuffleAvg_const.{u_1} {α : Type u_1} (l : List α) (c : ℝ) : shuffleAvg l (fun _ => c) = c :=
  listAvg_const (permutations'_ne_nil l) c

lemma shuffleAvg_perm.{u_1} {α : Type u_1} {l r : List α} (h : l.Perm r) (f : List α → ℝ) :
    shuffleAvg l f = shuffleAvg r f := listAvg_perm h.permutations' f

lemma shuffleAvg_congr.{u_1} {α : Type u_1} {l : List α} {f g : List α → ℝ}
    (h : ∀ r, r.Perm l → f r = g r) : shuffleAvg l f = shuffleAvg l g :=
  listAvg_congr fun _ hr => h _ (List.mem_permutations'.mp hr)

lemma shuffleAvg_mono.{u_1} {α : Type u_1} {l : List α} {f g : List α → ℝ}
    (h : ∀ r, r.Perm l → f r ≤ g r) : shuffleAvg l f ≤ shuffleAvg l g :=
  listAvg_mono fun _ hr => h _ (List.mem_permutations'.mp hr)

lemma shuffleAvg_nonneg.{u_1} {α : Type u_1} {l : List α} {f : List α → ℝ}
    (h : ∀ r, r.Perm l → 0 ≤ f r) : 0 ≤ shuffleAvg l f :=
  listAvg_nonneg fun _ hr => h _ (List.mem_permutations'.mp hr)

lemma shuffleAvg_add.{u_1} {α : Type u_1} (l : List α) (f g : List α → ℝ) :
    shuffleAvg l (fun r => f r+g r) = shuffleAvg l f+shuffleAvg l g := listAvg_add _ _ _
lemma shuffleAvg_sub.{u_1} {α : Type u_1} (l : List α) (f g : List α → ℝ) :
    shuffleAvg l (fun r => f r-g r) = shuffleAvg l f-shuffleAvg l g := listAvg_sub _ _ _
lemma shuffleAvg_mul.{u_1} {α : Type u_1} (l : List α) (c : ℝ) (f : List α → ℝ) :
    shuffleAvg l (fun r => c*f r) = c*shuffleAvg l f := listAvg_mul _ _ _

lemma shuffleAvg_sq_le.{u_1} {α : Type u_1} (l : List α) (f : List α → ℝ) :
    (shuffleAvg l f)^2 ≤ shuffleAvg l (fun r => (f r)^2) :=
  listAvg_sq_le (permutations'_ne_nil l) f

lemma listAvg_permutationsAux.{u_1} {α : Type u_1} (l : List α) (c : α) (f : List α → ℝ) :
    listAvg (List.permutations'Aux c l) f =
      favg (fun i : Fin (l.length+1) => f (l.insertIdx i c)) := by
  rw [listAvg_eq_favg]
  have he := favg_equiv (finCongr (List.length_permutations'Aux l c)).symm
    (fun i : Fin (List.permutations'Aux c l).length => f ((List.permutations'Aux c l).get i))
  rw [← he]
  congr 1
  funext i
  change f ((List.permutations'Aux c l).get ⟨i.val,_⟩) = _
  rw [List.get_permutations'Aux]

lemma shuffleAvg_cons.{u_1} {α : Type u_1} (l : List α) (c : α) (f : List α → ℝ) :
    shuffleAvg (c::l) f =
      shuffleAvg l (fun r => favg (fun i : Fin (l.length+1) => f (r.insertIdx i c))) := by
  unfold shuffleAvg
  rw [List.permutations', listAvg_flatMap _ _ _ (l.length+1) (by omega)
    (fun r hr => by rw [List.length_permutations'Aux, (List.mem_permutations'.mp hr).length_eq])]
  apply listAvg_congr
  intro r hr
  rw [listAvg_permutationsAux]
  have he := (List.mem_permutations'.mp hr).length_eq
  have hh := favg_equiv (finCongr (congrArg (fun x => x+1) he))
    (fun i : Fin (l.length+1) => f (r.insertIdx i c))
  exact hh

lemma ofFn_insertNth.{u_1} {α : Type u_1} {m : ℕ} (w : Fin m → α) (c : α) (i : Fin (m+1)) :
    List.ofFn (i.insertNth c w) = (List.ofFn w).insertIdx i.val c := by
  induction m with
  | zero =>
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    simp [Fin.insertNth_zero']
  | succ m ih =>
    obtain ⟨⟨a,w⟩,rfl⟩ := (Fin.consEquiv (fun _ : Fin (m+1) => α)).surjective w
    change List.ofFn (i.insertNth c (Fin.cons a w)) = (List.ofFn (Fin.cons a w)).insertIdx i.val c
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Fin.insertNth_zero']
    · rw [Fin.insertNth_succ_cons, List.ofFn_cons, List.ofFn_cons, Fin.val_succ,
        List.insertIdx_succ_cons, ih]

lemma favg_shuffle.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (m : ℕ) (f : List α → ℝ) :
    favg (fun w : Fin m → α => shuffleAvg (List.ofFn w) f) =
      favg (fun w : Fin m → α => f (List.ofFn w)) := by
  induction m generalizing f with
  | zero =>
    have he : ∀ w : Fin 0 → α, List.ofFn w = [] := fun _ => rfl
    simp only [he, shuffleAvg, List.permutations', listAvg]
    simp [favg_const]
  | succ m ih =>
    calc
      _ = favg (fun c : α => favg (fun w : Fin m → α =>
          shuffleAvg (c::List.ofFn w) f)) := by
        rw [favg_cons, favg_comm]
        simp only [List.ofFn_cons]
      _ = favg (fun c : α => favg (fun w : Fin m → α =>
          favg (fun i : Fin (m+1) => f ((List.ofFn w).insertIdx i c)))) := by
        congr 1
        funext c
        have hc (w : Fin m → α) : shuffleAvg (c :: List.ofFn w) f =
            shuffleAvg (List.ofFn w) (fun r => favg (fun i : Fin (m+1) => f (r.insertIdx i c))) := by
          rw [shuffleAvg_cons]
          apply shuffleAvg_congr
          intro r _
          exact favg_equiv (finCongr (congrArg (fun x => x+1) (List.length_ofFn (f := w))))
            (fun i : Fin (m+1) => f (r.insertIdx i c))
        simp only [hc]
        exact ih (fun r => favg (fun i : Fin (m+1) => f (r.insertIdx i c)))
      _ = favg (fun i : Fin (m+1) => favg (fun c : α => favg (fun w : Fin m → α =>
          f ((List.ofFn w).insertIdx i c)))) := by
        simp_rw [favg_comm (fun w : Fin m → α => fun i : Fin (m+1) =>
          f ((List.ofFn w).insertIdx i _))]
        exact favg_comm _
      _ = _ := by
        simp_rw [← ofFn_insertNth]
        have he (i : Fin (m+1)) :
            favg (fun c : α => favg (fun w : Fin m → α => f (List.ofFn (i.insertNth c w)))) =
            favg (fun v : Fin (m+1) → α => f (List.ofFn v)) :=
          (favg_insertNth i (fun v => f (List.ofFn v))).symm
        simp only [he, favg_const]

end RandomKSAT

end

end OAI
