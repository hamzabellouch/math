import Mathlib
import OAI.Analysis.Commutator.PartialWordReindex
import OAI.Analysis.Commutator.TracialL2Continuity

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder Topology

open Filter

namespace Kadison.FinitePatching.Words

variable {A J K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

include hτ in
lemma word_coefficients_norm_sub (x y : J → A) (k : K → ℤ)
    (hx : ∀ j,‖x j‖ ≤ 1) (hy : ∀ j,‖y j‖ ≤ 1)
    {δ : ℝ} (hxy : ∀ j,TracialL2.norm τ (x j-y j) ≤ δ)
    (v : PartialUnitary A) (l : List (Letter J K)) :
    TracialL2.norm τ (word x k v l-word y k v l) ≤ (l.length:ℝ)*δ := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hh : TracialL2.norm τ (letter x k v i-letter y k v i) ≤ δ := by
      change TracialL2.norm τ (x i.1*slotPower k v i.2-y i.1*slotPower k v i.2) ≤ δ
      rw [←sub_mul]
      exact (TracialL2.norm_mul_right τ hτ _ _).trans
        ((mul_le_of_le_one_right (TracialL2.norm_nonneg τ _) (slotPower_norm k v _)).trans (hxy _))
    rw [word_cons,word_cons]
    have h1 := TracialL2.norm_mul_sub_mul τ hτ (letter x k v i) (word x k v l)
      (letter y k v i) (word y k v l)
    have h2 := add_le_add
      ((mul_le_of_le_one_right (TracialL2.norm_nonneg τ _) (word_norm x k hx v l)).trans hh)
      ((mul_le_of_le_one_left (TracialL2.norm_nonneg τ _) (letter_norm y k hy v i)).trans ih)
    apply h1.trans (h2.trans_eq _)
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    ring

include hτ in
lemma trace_word_coefficients_norm_sub (hone : τ 1=1)
    (x y : J → A) (k : K → ℤ) (hx : ∀ j,‖x j‖ ≤ 1) (hy : ∀ j,‖y j‖ ≤ 1)
    {δ : ℝ} (hxy : ∀ j,TracialL2.norm τ (x j-y j) ≤ δ)
    (v : PartialUnitary A) (l : List (Letter J K)) :
    ‖τ (word x k v l)-τ (word y k v l)‖ ≤ (l.length:ℝ)*δ := by
  rw [←map_sub]
  exact (TracialL2.norm_trace_le τ hτ hone _).trans
    (word_coefficients_norm_sub τ hτ x y k hx hy hxy v l)

include hτ in
lemma moment_limit_of_dense_coefficients (hone : τ 1=1)
    (x : ℕ → A) (k : K → ℤ) (hx : ∀ j,‖x j‖ ≤ 1)
    (hden : ∀ a : A,‖a‖ ≤ 1 → τ a=0 → ∀ ε : ℝ,0<ε → ∃ j,TracialL2.norm τ (a-x j)<ε)
    (v : ℕ → PartialUnitary A)
    (hlim : ∀ l : List (Letter ℕ K),l≠[] → Valid l →
      Tendsto (fun n => τ (word x k (v n) l)) atTop (𝓝 0))
    (y : J → A) (hy : ∀ j,‖y j‖ ≤ 1) (hcy : ∀ j,τ (y j)=0)
    (l : List (Letter J K)) (hl : l≠[]) (hv : Valid l) :
    Tendsto (fun n => τ (word y k (v n) l)) atTop (𝓝 0) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε/(2*((l.length:ℝ)+1))
  have hδ : 0<δ := by dsimp [δ]; positivity
  choose f hf using (fun j => hden (y j) (hy j) (hcy j) δ hδ)
  have he : (l.length:ℝ)*δ ≤ ε/2 := by
    have hh : 2*((l.length:ℝ)+1)*δ=ε := by dsimp [δ]; field_simp
    nlinarith
  have hsmall := (hlim (l.map (mapLetter f id)) (by simpa using hl) (valid_map f id hv)).eventually
    (Metric.ball_mem_nhds (0:ℂ) (half_pos hε))
  filter_upwards [hsmall] with n hn
  have hh : ‖τ (word (x ∘ f) k (v n) l)‖<ε/2 := by
    simpa only [Metric.mem_ball,dist_zero_right,word_reindex,Function.comp_id] using hn
  have hd := trace_word_coefficients_norm_sub τ hτ hone y (x ∘ f) k hy
    (fun j => hx (f j)) (fun j => (hf j).le) (v n) l
  rw [dist_zero_right]
  have htri := norm_le_norm_sub_add (τ (word y k (v n) l)) (τ (word (x ∘ f) k (v n) l))
  linarith

end Kadison.FinitePatching.Words

end

end
end

end OAI
