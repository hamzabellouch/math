import Mathlib
import OAI.Analysis.Commutator.FiniteFullUnitaryTests
import OAI.Analysis.Commutator.PartialWordReindex

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder Topology

open Filter

namespace Kadison.FinitePatching

open Words

section Reindex

variable {A : Type*} [CStarAlgebra A]

lemma eventually_letter_truncate (x : ℕ → A) (k : ℕ → ℤ) (v : ℕ → PartialUnitary A)
    (i : Letter ℕ ℕ) : ∀ᶠ n : ℕ in atTop,
    letter (fun j => x (min j n)) (fun j => k (min j n)) (v n) i=letter x k (v n) i := by
  rcases i with ⟨j,s⟩
  cases s with
  | none =>
    filter_upwards [eventually_ge_atTop j] with n hn
    simp [letter,slotPower,min_eq_left hn]
  | some s =>
    cases s with
    | none =>
      filter_upwards [eventually_ge_atTop j] with n hn
      simp [letter,slotPower,min_eq_left hn]
    | some i =>
      filter_upwards [eventually_ge_atTop j,eventually_ge_atTop i] with n hn hi
      simp [letter,slotPower,min_eq_left hn,min_eq_left hi]

lemma eventually_word_truncate (x : ℕ → A) (k : ℕ → ℤ) (v : ℕ → PartialUnitary A)
    (l : List (Letter ℕ ℕ)) : ∀ᶠ n : ℕ in atTop,
    word (fun j => x (min j n)) (fun j => k (min j n)) (v n) l=word x k (v n) l := by
  induction l with
  | nil => exact Eventually.of_forall (fun _ => rfl)
  | cons i l ih =>
    filter_upwards [eventually_letter_truncate x k v i,ih] with n hn hl
    simp only [word_cons,hn,hl]

end Reindex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M R : VonNeumannAlgebra H) (hRM : R ≤ M)

variable (τ : M →ₚ[ℂ] ℂ) (hτ : ∀ a b : M,τ (a*b)=τ (b*a))

variable {ι : ℕ → Type*} [∀ n,Fintype (ι n)] [∀ n,LinearOrder (ι n)]
  [∀ n,Nonempty (ι n)]

variable (stage : ∀ n,Matrix (ι n) (ι n) ℂ →⋆ₐ[ℂ] M)

variable (hmono : ∀ {n m : ℕ},n ≤ m → (stage n).range ≤ (stage m).range)

include hRM hτ hmono in
theorem exists_countable_unitary_tests
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hirr : ∀ b : M,(∀ n (a : Matrix (ι n) (ι n) ℂ),stage n a*b=b*stage n a) →
      ∃ c : ℂ,b=algebraMap ℂ M c)
    (hgrow : Tendsto (fun n => (Fintype.card (ι n):ℝ)) atTop atTop)
    (hstage : ∀ n a,(stage n a : H →L[ℂ] H)∈R)
    (hdiffuse : DiffuseProjection.HasNoMinimalProjections R)
    (x : ℕ → M) (k : ℕ → ℤ) (hx : ∀ j,‖x j‖ ≤ 1)
    (hcenter : ∀ j,τ (x j)=0) (hk : ∀ i,k i≠0) :
    ∃ u : ℕ → unitary M, (∀ n, ((u n:M) : H →L[ℂ] H)∈R) ∧
      (∀ i,Tendsto (fun n => τ ((PartialUnitary.ofUnitary (u n)).power (k i))) atTop (𝓝 0)) ∧
      (∀ l : List (Letter ℕ ℕ), l≠[] → Valid l →
        Tendsto (fun n => τ (word x k (PartialUnitary.ofUnitary (u n)) l)) atTop (𝓝 0)) := by
  classical
  have hfinite (n : ℕ) := exists_full_unitary_finite_tests M R hRM τ hτ stage hmono
    hnormal hfaith hone hirr hgrow hstage hdiffuse
    (fun j : Fin (n+1) => x j) (fun i : Fin (n+1) => k i)
    (fun j => hx j) (fun j => hcenter j) (fun i => hk i) n
    (pow_pos (by norm_num : (0:ℝ)<1/2) n)
  choose u huR hu using hfinite
  have hbound (n : ℕ) : MomentBound τ (fun j => x (min j n)) (fun i => k (min i n))
      (PartialUnitary.ofUnitary (u n)) n ((1/2:ℝ)^n) := by
    let f : ℕ → Fin (n+1) := fun j => ⟨min j n,Nat.lt_succ_of_le (min_le_right _ _)⟩
    exact momentBound_reindex τ _ _ f f _ (hu n)
  have hlim : Tendsto (fun n : ℕ => (1/2:ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  refine ⟨u,huR,?_,?_⟩
  · intro i
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
    filter_upwards [eventually_ge_atTop i] with n hn
    simpa only [min_eq_left hn] using (hbound n).1 i
  · intro l hl hv
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
    filter_upwards [eventually_ge_atTop l.length,
      eventually_word_truncate x k (fun n => PartialUnitary.ofUnitary (u n)) l] with n hn he
    rw [←he]
    exact (hbound n).2 l hl hn hv

end Kadison.FinitePatching

end

end
end

end OAI
