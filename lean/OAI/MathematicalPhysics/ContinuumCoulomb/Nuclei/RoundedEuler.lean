import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.EulerApproximation

namespace OAI

/-! Grid rounding after every Euler step controls the size of rational
intermediates. The rounding error is accumulated in the actual trajectory
estimate, separately from the field sampling and time discretization. -/

noncomputable section
namespace ContinuumCoulomb.EulerApproximation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def roundedIterate (round : E → E) (h : ℝ) (evaluate : ℕ → E → E)
    (x₀ : E) : ℕ → E
  | 0 => x₀
  | n+1 => round (roundedIterate round h evaluate x₀ n +
      h • evaluate n (roundedIterate round h evaluate x₀ n))

theorem rounded_sequence_error (v evaluate : ℕ → E → E) (z y : ℕ → E)
    (N : ℕ) {h L δ D R : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hδ : 0 ≤ δ) (hD : 0 ≤ D) (hR : 0 ≤ R)
    (hLip : ∀ n < N, ∀ x, ‖v n x-v n (z n)‖ ≤ L*‖x-z n‖)
    (heval : ∀ n < N, ‖evaluate n (y n)-v n (y n)‖ ≤ δ)
    (hdefect : ∀ n < N, ‖z n+h • v n (z n)-z (n+1)‖ ≤ D)
    (hround : ∀ n < N, ‖y (n+1)-(y n+h • evaluate n (y n))‖ ≤ R) :
    ‖y N-z N‖ ≤
      (‖y 0-z 0‖+(N:ℝ)*(h*δ+D+R))*Real.exp ((N:ℝ)*(h*L)) := by
  let u : ℕ → ℝ := fun n => ‖y n-z n‖
  have hb : 0 ≤ h*δ+D+R := by positivity
  have hs (n : ℕ) (hn : n < N) : u (n+1) ≤ (1+h*L)*u n+(h*δ+D+R) := by
    have ht := norm_sub_le_norm_sub_add_norm_sub (y (n+1))
      (y n+h • evaluate n (y n)) (z (n+1))
    have he := step_error v evaluate z (y n) n hh (hLip n hn _)
      (heval n hn) (hdefect n hn)
    dsimp [u]
    linarith [hround n hn]
  exact finite_recurrence_bound u N (mul_nonneg hh hL) hb (norm_nonneg _) hs N le_rfl

theorem rounded_iterate_error (round : E → E) (v evaluate : ℕ → E → E)
    (z : ℕ → E) (x₀ : E) (N : ℕ) {h L δ D R : ℝ}
    (hh : 0 ≤ h) (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hD : 0 ≤ D) (hR : 0 ≤ R)
    (hLip : ∀ n < N, ∀ x, ‖v n x-v n (z n)‖ ≤ L*‖x-z n‖)
    (heval : ∀ n < N, ∀ x, ‖evaluate n x-v n x‖ ≤ δ)
    (hdefect : ∀ n < N, ‖z n+h • v n (z n)-z (n+1)‖ ≤ D)
    (hround : ∀ x, ‖round x-x‖ ≤ R) :
    ‖roundedIterate round h evaluate x₀ N-z N‖ ≤
      (‖x₀-z 0‖+(N:ℝ)*(h*δ+D+R))*Real.exp ((N:ℝ)*(h*L)) := by
  exact rounded_sequence_error v evaluate z (roundedIterate round h evaluate x₀) N
    hh hL hδ hD hR hLip (fun n hn => heval n hn _)
    hdefect (fun n _ => hround _)

theorem uniform_flow_local_defect (v : ℝ → E → E) (z : ℝ → E)
    {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hz : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivWithinAt z (v t (z t)) (Set.Icc (0:ℝ) 1) t)
    (hbound : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖v t (z t)‖ ≤ M)
    (hLip : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1,
      ‖v s (z s)-v t (z t)‖ ≤ L*(|s-t|+‖z s-z t‖))
    {t h : ℝ} (ht : 0 ≤ t) (hh : 0 ≤ h) (hth : t+h ≤ 1) :
    ‖z t+h • v t (z t)-z (t+h)‖ ≤ L*(1+M)*h^2 := by
  have hsub : Set.Icc t (t+h) ⊆ Set.Icc (0:ℝ) 1 := by
    intro s hs
    exact ⟨ht.trans hs.1, hs.2.trans hth⟩
  exact local_defect v z hh hL hM
    (fun s hs => (hz s (hsub hs)).mono hsub)
    (fun s hs => hbound s (hsub hs))
    (fun s hs => hLip s (hsub hs) t ⟨ht, by linarith⟩)

/-- Projection onto a fixed box may move an inaccurate Euler proposal a
long way, but it only improves its distance to a trajectory inside that
box. This form of the recurrence handles such projections directly. -/
theorem projected_sequence_error (v evaluate : ℕ → E → E) (z y : ℕ → E)
    (N : ℕ) {h L δ D R : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hδ : 0 ≤ δ) (hD : 0 ≤ D) (hR : 0 ≤ R)
    (hLip : ∀ n < N, ∀ x, ‖v n x-v n (z n)‖ ≤ L*‖x-z n‖)
    (heval : ∀ n < N, ‖evaluate n (y n)-v n (y n)‖ ≤ δ)
    (hdefect : ∀ n < N, ‖z n+h • v n (z n)-z (n+1)‖ ≤ D)
    (hproject : ∀ n < N, ‖y (n+1)-z (n+1)‖ ≤
      ‖y n+h • evaluate n (y n)-z (n+1)‖+R) :
    ‖y N-z N‖ ≤
      (‖y 0-z 0‖+(N:ℝ)*(h*δ+D+R))*Real.exp ((N:ℝ)*(h*L)) := by
  let u : ℕ → ℝ := fun n => ‖y n-z n‖
  have hb : 0 ≤ h*δ+D+R := by positivity
  have hs (n : ℕ) (hn : n < N) : u (n+1) ≤ (1+h*L)*u n+(h*δ+D+R) := by
    have he := step_error v evaluate z (y n) n hh (hLip n hn _)
      (heval n hn) (hdefect n hn)
    dsimp [u]
    linarith [hproject n hn]
  exact finite_recurrence_bound u N (mul_nonneg hh hL) hb (norm_nonneg _) hs N le_rfl

theorem sampled_unit_error (v : ℝ → E → E) (z : ℝ → E)
    (evaluate : ℕ → E → E) (y : ℕ → E) {N : ℕ} (hN : 0 < N)
    {L M δ R : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hR : 0 ≤ R)
    (hz : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivWithinAt z (v t (z t)) (Set.Icc (0:ℝ) 1) t)
    (hbound : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖v t (z t)‖ ≤ M)
    (hLip : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ x w,
      ‖v s x-v t w‖ ≤ L*(|s-t|+‖x-w‖))
    (heval : ∀ n < N, ‖evaluate n (y n)-v ((n:ℝ)/N) (y n)‖ ≤ δ)
    (hproject : ∀ n < N,
      ‖y (n+1)-z (((n:ℝ)+1)/N)‖ ≤
        ‖y n+(N:ℝ)⁻¹ • evaluate n (y n)-z (((n:ℝ)+1)/N)‖+R) :
    ‖y N-z 1‖ ≤
      (‖y 0-z 0‖+δ+L*(1+M)/(N:ℝ)+(N:ℝ)*R)*Real.exp L := by
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  have hNN : (N:ℝ) ≠ 0 := hNp.ne'
  let zseq : ℕ → E := fun n => z ((n:ℝ)/N)
  let vseq : ℕ → E → E := fun n => v ((n:ℝ)/N)
  have htime (n : ℕ) (hn : n ≤ N) : (n:ℝ)/N ∈ Set.Icc (0:ℝ) 1 := by
    constructor
    · positivity
    · exact (div_le_one hNp).mpr (by exact_mod_cast hn)
  have hnext (n : ℕ) : (n:ℝ)/N+(N:ℝ)⁻¹ = ((n:ℝ)+1)/N := by ring
  have hl (n : ℕ) (hn : n < N) (x : E) :
      ‖vseq n x-vseq n (zseq n)‖ ≤ L*‖x-zseq n‖ := by
    simpa only [vseq,zseq,sub_self,abs_zero,zero_add] using
      hLip ((n:ℝ)/N) (htime n hn.le) ((n:ℝ)/N) (htime n hn.le) x (zseq n)
  have hd (n : ℕ) (hn : n < N) :
      ‖zseq n+(N:ℝ)⁻¹ • vseq n (zseq n)-zseq (n+1)‖ ≤
        L*(1+M)*((N:ℝ)⁻¹)^2 := by
    have hnxt : (n:ℝ)/N+(N:ℝ)⁻¹ ≤ 1 := by
      rw [hnext]
      apply (div_le_one hNp).mpr
      exact_mod_cast (show n+1 ≤ N by omega)
    have he := uniform_flow_local_defect v z hL hM hz hbound
      (fun s hs t ht => hLip s hs t ht (z s) (z t))
      (t := (n:ℝ)/N) (h := (N:ℝ)⁻¹) (htime n hn.le).1 (by positivity) hnxt
    simpa only [zseq,vseq,hnext,Nat.cast_add,Nat.cast_one] using he
  have hp (n : ℕ) (hn : n < N) :
      ‖y (n+1)-zseq (n+1)‖ ≤ ‖y n+(N:ℝ)⁻¹ • evaluate n (y n)-zseq (n+1)‖+R := by
    simpa only [zseq,Nat.cast_add,Nat.cast_one] using hproject n hn
  have he := projected_sequence_error vseq evaluate zseq y N (by positivity) hL hδ
    (by positivity) hR hl heval hd hp
  have hexp : (N:ℝ)*((N:ℝ)⁻¹*L) = L := by field_simp
  have hsum : (N:ℝ)*((N:ℝ)⁻¹*δ+L*(1+M)*((N:ℝ)⁻¹)^2+R) =
      δ+L*(1+M)/(N:ℝ)+(N:ℝ)*R := by field_simp
  have hsum' : (N:ℝ)*((N:ℝ)⁻¹*δ+(L*(1+M)*((N:ℝ)⁻¹)^2+R)) =
      δ+(L*(1+M)/(N:ℝ)+(N:ℝ)*R) := by simpa only [add_assoc] using hsum
  simpa only [zseq,div_self hNN,Nat.cast_zero,zero_div,hexp,add_assoc,hsum'] using he

end ContinuumCoulomb.EulerApproximation

end

end OAI
