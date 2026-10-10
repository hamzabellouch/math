import OAI.MathematicalPhysics.Heisenberg.CycleWeights

namespace OAI

noncomputable section
open scoped Classical

namespace Heisenberg.Geometry

lemma reach_rectangle {d : ℕ} (U : Set (Site d)) (x y : Site d)
    (hU : ∀ z, (∀ j, min (x j) (y j) ≤ z j ∧ z j ≤ max (x j) (y j)) → z ∈ U) :
    Reach U x y := by
  let v (s : Finset (Fin d)) : Site d := fun j => if j ∈ s then y j else x j
  have hv : ∀ s : Finset (Fin d), Reach U x (v s) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa [v] using reach_refl U x
    | @insert j s hj ih =>
      apply reach_trans ih
      have hstart : Function.update (v s) j (x j) = v s := by
        apply Function.update_eq_self_iff.mpr
        simp [v, hj]
      have hend : Function.update (v s) j (y j) = v (insert j s) := by
        funext k
        by_cases hk : k = j
        · subst k; simp [v]
        · simp [v, hk]
      rw [← hstart, ← hend]
      apply reach_axis
      intro t ht₁ ht₂
      apply hU
      intro k
      by_cases hk : k = j
      · subst k; simpa using And.intro ht₁ ht₂
      · simp only [Function.update_of_ne hk, v]
        split_ifs
        · exact ⟨min_le_right .., le_max_right ..⟩
        · exact ⟨min_le_left .., le_max_left ..⟩
  simpa [v] using hv Finset.univ

lemma shell_to_corner {d : ℕ} (hd : 2 ≤ d) (r : ℤ) (hr : 0 ≤ r)
    (x : Site d) (hx : x ∈ Shell r) :
    Reach (Shell r) x (fun _ => r) := by
  obtain ⟨hbox, j, hj⟩ := hx
  let y : Site d := fun k => if k = j then x j else r
  have hy : Reach (Shell r) x y := by
    apply reach_rectangle
    intro z hz
    refine ⟨?_, j, ?_⟩
    · intro k
      have h := hz k
      have hbound := hbox k
      have hybound : |y k| ≤ r := by
        dsimp [y]; split_ifs
        · exact hbox j
        · simp only [abs_of_nonneg hr, le_refl]
      rw [abs_le] at hbound hybound ⊢
      exact ⟨le_trans (le_min hbound.1 hybound.1) h.1,
        le_trans h.2 (max_le hbound.2 hybound.2)⟩
    · have h := hz j
      have hzj : z j = x j := by
        simp only [y, ite_eq_left rfl, min_self, max_self] at h
        exact le_antisymm h.2 h.1
      simpa [hzj] using hj
  obtain ⟨k, hkj⟩ : ∃ k : Fin d, k ≠ j := by
    have : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr hd
    exact exists_ne j
  apply reach_trans hy
  have hstart : Function.update y j (x j) = y := by
    apply Function.update_eq_self_iff.mpr
    simp [y]
  have hend : Function.update y j r = (fun _ => r) := by
    funext a
    by_cases ha : a = j
    · subst a; simp
    · simp [y, ha]
  rw [← hstart, ← hend]
  apply reach_axis
  intro t ht₁ ht₂
  refine ⟨?_, k, ?_⟩
  · intro a
    by_cases ha : a = j
    · subst a
      simp only [Function.update_self]
      rw [abs_le]
      have hb := (abs_le.mp (hbox j))
      exact ⟨le_trans (le_min hb.1 (by omega)) ht₁,
        le_trans ht₂ (max_le hb.2 le_rfl)⟩
    · simp [y, ha, abs_of_nonneg hr]
  · simp [y, hkj, abs_of_nonneg hr]

lemma shell_connected {d : ℕ} (hd : 2 ≤ d) (r : ℤ) (hr : 0 ≤ r)
    (x y : Site d) (hx : x ∈ Shell r) (hy : y ∈ Shell r) :
    Reach (Shell r) x y :=
  reach_trans (shell_to_corner hd r hr x hx) (reach_symm (shell_to_corner hd r hr y hy))


abbrev Direction (d : ℕ) := Fin d × Bool

def Ray {d : ℕ} (x : Site d) (q : Direction d) (z : Site d) : Prop :=
  (if q.2 then x q.1 < z q.1 else z q.1 < x q.1) ∧
    ∀ k, k ≠ q.1 → z k = x k

lemma ray_unique {d : ℕ} (x z : Site d) (q q' : Direction d)
    (h : Ray x q z) (h' : Ray x q' z) : q = q' := by
  have hne : z q.1 ≠ x q.1 := by
    have hlt := h.1
    cases hb : q.2 <;> simp only [hb, Bool.false_eq_true, ↓reduceIte] at hlt
    · exact ne_of_lt hlt
    · exact ne_of_gt hlt
  have hj : q.1 = q'.1 := by
    by_contra hn
    exact hne (h'.2 q.1 hn)
  apply Prod.ext hj
  have h₁ := h.1
  have h₂ := h'.1
  rw [← hj] at h₂
  cases hb : q.2 <;> cases hb' : q'.2 <;>
    simp only [hb, hb', Bool.false_eq_true, ↓reduceIte] at h₁ h₂ ⊢ <;> omega

lemma exists_clear_ray {d : ℕ} (x : Site d) (F : Finset (Site d))
    (hF : F.card < 2 * d) : ∃ q : Direction d, ∀ z ∈ F, ¬ Ray x q z := by
  by_contra hn
  push Not at hn
  choose z hzF hz using hn
  let f : Direction d → F := fun q => ⟨z q, hzF q⟩
  have hf : Function.Injective f := by
    intro q q' he
    have hzEq : z q = z q' := congrArg Subtype.val he
    exact ray_unique x (z q) q q' (hz q) (hzEq ▸ hz q')
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    Fintype.card_coe] at hc
  omega

lemma shell_radius_unique {d : ℕ} (x : Site d) (r t : ℤ)
    (hr : x ∈ Shell r) (ht : x ∈ Shell t) : r = t := by
  obtain ⟨hrbox, j, hj⟩ := hr
  obtain ⟨htbox, k, hk⟩ := ht
  exact le_antisymm (hj ▸ htbox j) (hk ▸ hrbox k)

lemma exists_clean_shell {d : ℕ} (K : ℤ) (F : Finset (Site d))
    (hF : F.card < 2 * d) :
    ∃ r : ℤ, K < r ∧ r ≤ K + 2 * d ∧ ∀ z ∈ F, z ∉ Shell r := by
  by_contra hn
  have hbad : ∀ n : Fin (2 * d), ∃ z ∈ F, z ∈ Shell (K + 1 + n.val) := by
    intro n
    have hl : K < K + 1 + (n.val : ℤ) := by omega
    have hu : K + 1 + (n.val : ℤ) ≤ K + 2 * d := by omega
    by_contra hn'
    push Not at hn'
    exact hn ⟨K + 1 + n.val, hl, hu, hn'⟩
  choose z hzF hz using hbad
  let f : Fin (2 * d) → F := fun n => ⟨z n, hzF n⟩
  have hf : Function.Injective f := by
    intro n n' he
    have hzEq : z n = z n' := congrArg Subtype.val he
    have hn := shell_radius_unique (z n) _ _ (hz n) (hzEq ▸ hz n')
    apply Fin.ext
    omega
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin, Fintype.card_coe] at hc
  omega

lemma reach_shell {d : ℕ} (r : ℤ) (hr : 0 ≤ r) (x : Site d)
    (hx : x ∈ Box r) (F : Finset (Site d)) (hxF : x ∉ F) (hF : F.card < 2 * d) :
    ∃ y ∈ Shell r, Reach (Box r \ (F : Set (Site d))) x y := by
  obtain ⟨q, hq⟩ := exists_clear_ray x F hF
  let b : ℤ := if q.2 then r else -r
  let y := Function.update x q.1 b
  have hb : |b| = r := by
    dsimp [b]; split_ifs <;> simp [abs_of_nonneg hr]
  have hybox : y ∈ Box r := by
    intro k
    by_cases hk : k = q.1
    · subst k; simpa [y] using hb.le
    · simpa [y, hk] using hx k
  have hyshell : y ∈ Shell r := ⟨hybox, q.1, by simpa [y] using hb⟩
  refine ⟨y, hyshell, ?_⟩
  have hstart := Function.update_eq_self q.1 x
  rw [← hstart]
  apply reach_axis
  intro t ht₁ ht₂
  constructor
  · intro k
    by_cases hk : k = q.1
    · subst k
      simp only [Function.update_self]
      rw [abs_le]
      have ha := abs_le.mp (hx q.1)
      have hb' := abs_le.mp hb.le
      exact ⟨le_trans (le_min ha.1 hb'.1) ht₁,
        le_trans ht₂ (max_le ha.2 hb'.2)⟩
    · simpa [hk] using hx k
  · intro htF
    by_cases ht : t = x q.1
    · subst t
      exact hxF (by simpa using htF)
    · apply hq (Function.update x q.1 t) htF
      refine ⟨?_, ?_⟩
      · simp only [Function.update_self]
        cases hq₂ : q.2
        · have hb' : b = -r := by simp [b, hq₂]
          have ha := abs_le.mp (hx q.1)
          simp only [Bool.false_eq_true, ↓reduceIte]
          have htmax : max (x q.1) b = x q.1 := max_eq_left (by omega)
          rw [htmax] at ht₂
          omega
        · have hb' : b = r := by simp [b, hq₂]
          have ha := abs_le.mp (hx q.1)
          simp only [↓reduceIte]
          have htmin : min (x q.1) b = x q.1 := min_eq_left (by omega)
          rw [htmin] at ht₁
          omega
      · intro k hk
        simp [hk]


lemma box_mono {d : ℕ} {r t : ℤ} (h : r ≤ t) : (Box r : Set (Site d)) ⊆ Box t :=
  fun _ hx j => (hx j).trans h

theorem finite_obstacle_connection {d : ℕ} (hd : 2 ≤ d) (K : ℤ) (hK : 0 ≤ K)
    (x y : Site d) (hx : x ∈ Box K) (hy : y ∈ Box K) (F : Finset (Site d))
    (hxF : x ∉ F) (hyF : y ∉ F) (hF : F.card < 2 * d) :
    Reach (Box (K + 2 * d) \ (F : Set (Site d))) x y := by
  obtain ⟨r, hKr, hrK, hrF⟩ := exists_clean_shell K F hF
  have hr : 0 ≤ r := by omega
  obtain ⟨a, ha, hxa⟩ := reach_shell r hr x (box_mono hKr.le hx) F hxF hF
  obtain ⟨b, hb, hyb⟩ := reach_shell r hr y (box_mono hKr.le hy) F hyF hF
  have hab : Reach (Box r \ (F : Set (Site d))) a b := by
    apply reach_mono _ (shell_connected hd r hr a b ha hb)
    intro z hz
    exact ⟨hz.1, fun hzF => hrF z hzF hz⟩
  apply reach_mono _ (hxa.trans (hab.trans (reach_symm hyb)))
  intro z hz
  exact ⟨box_mono hrK hz.1, hz.2⟩

def latticeGraph {d : ℕ} (U : Set (Site d)) : SimpleGraph (Site d) where
  Adj x y := Step x y ∧ x ∈ U ∧ y ∈ U
  symm := ⟨fun _ _ h => ⟨step_symm h.1, h.2.2, h.2.1⟩⟩
  loopless := ⟨by
    intro x h
    obtain ⟨j, h, _⟩ := h.1
    omega⟩

lemma reach_has_simple_path {d : ℕ} (U : Set (Site d)) (x y : Site d)
    (h : Reach U x y) : ∃ p : (latticeGraph U).Walk x y, p.IsPath := by
  apply SimpleGraph.Reachable.exists_isPath
  exact (SimpleGraph.reachable_iff_reflTransGen ..).mpr h

def boxFinset (d r : ℕ) : Finset (Site d) :=
  Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(r : ℤ)) r)

@[simp] lemma mem_boxFinset (d r : ℕ) (x : Site d) :
    x ∈ boxFinset d r ↔ x ∈ Box r := by
  simp only [boxFinset, Fintype.mem_piFinset, Finset.mem_Icc, Box, Set.mem_ofPred_eq, abs_le]

lemma card_boxFinset (d r : ℕ) : (boxFinset d r).card = (2 * r + 1) ^ d := by
  simp only [boxFinset, Fintype.card_piFinset, Int.card_Icc]
  have hc : ((r : ℤ) + 1 + (r : ℤ)).toNat = 2 * r + 1 := by omega
  simp [hc]

lemma path_support_mem {d : ℕ} (U : Set (Site d)) (x y : Site d)
    (hx : x ∈ U) (p : (latticeGraph U).Walk x y) : ∀ z ∈ p.support, z ∈ U := by
  induction p with
  | nil => simpa using hx
  | @cons a b c hab p ih =>
    intro z hz
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hx
    · exact ih hab.2.2 z hz

lemma simple_path_length_bound {d : ℕ} (U : Set (Site d)) (r : ℕ)
    (hU : U ⊆ Box r) (x y : Site d) (hx : x ∈ U)
    (p : (latticeGraph U).Walk x y) (hp : p.IsPath) :
    p.length < (2 * r + 1) ^ d := by
  have hs : p.support.toFinset ⊆ boxFinset d r := by
    intro z hz
    exact (mem_boxFinset ..).mpr (hU (path_support_mem U x y hx p z (List.mem_toFinset.mp hz)))
  have hc := Finset.card_le_card hs
  rw [List.toFinset_card_of_nodup hp.support_nodup, SimpleGraph.Walk.length_support,
    card_boxFinset] at hc
  omega

end Heisenberg.Geometry
end

end OAI
