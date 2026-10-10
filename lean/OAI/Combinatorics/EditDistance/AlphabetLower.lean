import OAI.Combinatorics.EditDistance.LowerBound
import OAI.Combinatorics.EditDistance.DistortionMonotonicity

namespace OAI

/-!
# Uniform lower bounds under binary alphabet embeddings
-/

namespace EditDistortion
universe u

lemma coordinate_norm {X : Type u} [Fintype X] (x : X) : ‖coordinateEmbedding X x‖ = 1 := by
  classical
  change ‖lp.single (E := fun _ : ℕ => ℝ) 1 ((Fintype.equivFin X x).val) (1 : ℝ)‖ = 1
  rw [lp.norm_single (by norm_num)]
  norm_num

lemma coordinate_separation {X : Type u} [Fintype X] (x y : X) (hxy : x ≠ y) :
    1 ≤ ‖coordinateEmbedding X x-coordinateEmbedding X y‖ := by
  classical
  let e : X ↪ ℕ := (Fintype.equivFin X).toEmbedding.trans ⟨Fin.val,Fin.val_injective⟩
  have hne : e x ≠ e y := fun h => hxy (e.injective h)
  have h := lp.norm_apply_le_norm (by norm_num : (1 : ENNReal) ≠ 0)
    (coordinateEmbedding X x - coordinateEmbedding X y) (e x)
  have he : (coordinateEmbedding X x-coordinateEmbedding X y) (e x) = 1 := by
    change lp.single (E := fun _ : ℕ => ℝ) 1 (e x) (1 : ℝ) (e x) -
      lp.single (E := fun _ : ℕ => ℝ) 1 (e y) (1 : ℝ) (e x) = 1
    rw [lp.single_apply_self,lp.single_apply_ne (E := fun _ : ℕ => ℝ) 1 (e y) (1 : ℝ) hne]
    norm_num
  simpa only [he,norm_one] using h

theorem alphabet_coarse_upper (Alpha : Type u) [Fintype Alpha] [Nonempty Alpha]
    {d : ℕ} (hd : 1 ≤ d) : E Alpha d ≤ 2*(d : ℝ) := by
  classical
  let : Finite (Words Alpha d) := finite_words Alpha d
  let : Fintype (Words Alpha d) := Fintype.ofFinite _
  let x : Words Alpha d := ⟨[],by simp⟩
  let y : Words Alpha d := ⟨[Classical.arbitrary Alpha],by simpa using hd⟩
  let : Nontrivial (Words Alpha d) := ⟨⟨x,y,by simp [x,y]⟩⟩
  let f := coordinateEmbedding (Words Alpha d)
  apply (leastDistortion_le _ (fun v => edit_real_diag v.val)
    (fun v w h => edit_real_pos v.val w.val (fun hh => h (Subtype.ext hh))) f).trans
  apply distortion_le_of_bounds _
    (fun v w h => edit_real_pos v.val w.val (fun hh => h (Subtype.ext hh))) f (by norm_num)
  · intro v w
    by_cases h : v = w
    · subst w
      simp [edit_real_diag]
    · have hp : (1 : ℝ) ≤ edit v.val w.val := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr
          (mt (cost_eq_zero_iff (s := true)).mp (fun hh => h (Subtype.ext hh)))
      have hh := norm_sub_le (f v) (f w)
      have hv : ‖f v‖ = 1 := coordinate_norm v
      have hw : ‖f w‖ = 1 := coordinate_norm w
      nlinarith
  · intro v w
    by_cases h : v = w
    · subst w
      simp [edit_real_diag]
    · have hs : (1 : ℝ) ≤ ‖f v-f w‖ := coordinate_separation v w h
      have he : (edit v.val w.val : ℝ) ≤ d := by
        exact_mod_cast (edit_le_max_length v.val w.val).trans
          (max_le v.property w.property)
      nlinarith [Nat.cast_nonneg (α := ℝ) d]

lemma alphabet_values_bddAbove {d : ℕ} (hd : 1 ≤ d) :
    BddAbove {r : ℝ | ∃ n : ℕ, 2 ≤ n ∧ r = E (Fin n) d} := by
  refine ⟨2*(d : ℝ),?_⟩
  rintro r ⟨n,hn,rfl⟩
  let : NeZero n := ⟨by omega⟩
  exact alphabet_coarse_upper (Fin n) hd

lemma alphabet_le_sup {d n : ℕ} (hd : 1 ≤ d) (hn : 2 ≤ n) : E (Fin n) d ≤ alphabetSup d :=
  le_csSup (alphabet_values_bddAbove hd) ⟨n,hn,rfl⟩

end EditDistortion

namespace EditLower

universe u

open EditDistortion

theorem all_lower_clauses : ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    (∀ (Alpha : Type u) [Fintype Alpha], 2 ≤ Fintype.card Alpha →
      exponentScale c d ≤ E Alpha d) ∧ BinaryWitness c d ∧
      exponentScale c d ≤ alphabetSup d := by
  obtain ⟨D,hD⟩ := Filter.eventually_atTop.mp eventually_length_witness
  refine ⟨1/1200,by norm_num,max D 1,?_⟩
  intro d hd
  obtain ⟨n,hn,S,hfin,hne,hnt,hlen,hs⟩ := hD d ((le_max_left _ _).trans hd)
  refine ⟨?_,⟨n,hn,S,hfin,hne,hlen,hs⟩,?_⟩
  · intro Alpha inst hAlpha
    exact hs.trans (binary_subset_lower Alpha hAlpha hn S hfin hnt hlen)
  · exact (hs.trans (binary_subset_lower (Fin 2) (by simp) hn S hfin hnt hlen)).trans
      (alphabet_le_sup ((le_max_right _ _).trans hd) (by omega))

end EditLower

end OAI
