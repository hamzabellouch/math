import Mathlib
import OAI.Computability.VertexCover.PCP.PoweringLazy
import OAI.Computability.VertexCover.PCP.PoweringReturn

namespace OAI

                                                                                        

namespace UniqueGames.Foundations.PCP.PoweringWitness

open PoweringWalks SpectralReturn PoweringReturn PoweringLazy
open PoweringMoment (bit)

variable {V D : Type*}

theorem iterate_mul_const [Fintype D] (G : PortGraph V D)
    (n : Nat) («c» : ℝ) (h : V → ℝ) :
    iterateOperator G n (fun x => «c» * h x) =
      fun x => «c» * iterateOperator G n h x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change averagingOperator G (iterateOperator G n (fun x => «c» * h x)) =
      fun x => «c» * averagingOperator G (iterateOperator G n h) x
    rw [ih]
    funext v
    exact mean_mul_left «c» (fun d => iterateOperator G n h (G.rot (v, d)).1)

noncomputable def endpointWitness (G : PortGraph V D) (bad : Edge V D → Bool)
    (φ ψ : Edge V D → V → ℝ) (n : Nat) (k : Fin (n + 1))
    (w : Walk V D (n + 1)) : ℝ :=
  bit (bad (edgeAt G n w k) = true) *
    φ (edgeAt G n w k) w.1 * ψ (edgeAt G n w k) (endpoint G w)

noncomputable def vertexWitness (G : PortGraph V D) (bad : Edge V D → Bool)
    (f : V → V → ℝ) (n : Nat) (k : Fin (n + 1)) :
    Walk V D (n + 1) → ℝ :=
  endpointWitness G bad (fun e => f e.1) (fun e => f (next G e.1 e.2)) n k

theorem endpoint_lower_bound [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (n : Nat) (k : Fin (n + 1)) (bad : Edge V D → Bool)
    (φ ψ : Edge V D → V → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hL : ∀ e, bad e = true → a ≤ iterateOperator G k.val (φ e) e.1)
    (hR : ∀ e, bad e = true →
      a ≤ iterateOperator G (n - k.val) (ψ e) (next G e.1 e.2)) :
    edgeDensity bad * a ^ 2 ≤ mean (endpointWitness G bad φ ψ n k) := by
  have hfactor : mean (endpointWitness G bad φ ψ n k) =
      mean (fun e : Edge V D =>
        (bit (bad e = true) * iterateOperator G k.val (φ e) e.1) *
          iterateOperator G (n - k.val) (ψ e) (next G e.1 e.2)) := by
    unfold endpointWitness
    rw [mean_edge_endpoints G n k (fun e x => bit (bad e = true) * φ e x) ψ]
    simp_rw [iterate_mul_const]
  have hbitMean : mean (fun e : Edge V D => bit (bad e = true)) = edgeDensity bad := by
    calc
      _ = mean (fun v : V => mean (fun d : D => bit (bad (v, d) = true))) :=
        mean_prod (A := V) (B := D) (fun e => bit (bad e = true))
      _ = edgeDensity bad := by simp only [mean_edge_bit, edgeDensity]
  calc
    edgeDensity bad * a ^ 2 =
        mean (fun e : Edge V D => bit (bad e = true) * a ^ 2) := by
      rw [mean_mul_right, hbitMean]
    _ ≤ mean (fun e : Edge V D =>
        (bit (bad e = true) * iterateOperator G k.val (φ e) e.1) *
          iterateOperator G (n - k.val) (ψ e) (next G e.1 e.2)) := by
      apply mean_mono
      intro e
      cases hb : bad e with
      | false => simp [bit]
      | true =>
        have hprod := mul_le_mul (hL e hb) (hR e hb) ha (ha.trans (hL e hb))
        simpa [bit, hb, pow_two] using hprod
    _ = mean (endpointWitness G bad φ ψ n k) := hfactor.symm

theorem lazy_middle_witness_mean [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (q M : Nat) (hq : 1 ≤ q) (hM : 1 ≤ M)
    (k : Fin (2 * (4 * q * M) ^ 2 + 1))
    (hlo : (4 * q * M) ^ 2 - M ≤ k.val)
    (hhi : k.val ≤ (4 * q * M) ^ 2 + M)
    (bad : Edge V (Bool × D) → Bool) (f : V → V → ℝ)
    (hf : ∀ u w, f u w ∈ Set.Icc (0 : ℝ) 1)
    (hmodal : ∀ u, 1 / (q : ℝ) ≤
      iterateOperator (lazyGraph G) ((4 * q * M) ^ 2) (f u) u) :
    edgeDensity bad / (4 * (q : ℝ) ^ 2) ≤
      mean (vertexWitness (lazyGraph G) bad f (2 * (4 * q * M) ^ 2) k) := by
  have hk : k.val ≤ 2 * (4 * q * M) ^ 2 := Nat.le_of_lt_succ k.isLt
  have hslo : (4 * q * M) ^ 2 - M ≤ 2 * (4 * q * M) ^ 2 - k.val := by omega
  have hshi : 2 * (4 * q * M) ^ 2 - k.val ≤ (4 * q * M) ^ 2 + M := by omega
  have ha : (0 : ℝ) ≤ 1 / (2 * (q : ℝ)) := by positivity
  have hbound := endpoint_lower_bound (lazyGraph G) (2 * (4 * q * M) ^ 2) k bad
    (fun e => f e.1) (fun e => f (next (lazyGraph G) e.1 e.2))
    (1 / (2 * (q : ℝ))) ha
    (by
      intro e _
      exact lazy_endpoint_modal_transfer G q M k.val hq hM hlo hhi
        (f e.1) (hf e.1) e.1 (hmodal e.1))
    (by
      intro e _
      exact lazy_endpoint_modal_transfer G q M (2 * (4 * q * M) ^ 2 - k.val)
        hq hM hslo hshi (f (next (lazyGraph G) e.1 e.2))
        (hf (next (lazyGraph G) e.1 e.2)) (next (lazyGraph G) e.1 e.2)
        (hmodal (next (lazyGraph G) e.1 e.2)))
  have hscale : edgeDensity bad * (1 / (2 * (q : ℝ))) ^ 2 =
      edgeDensity bad / (4 * (q : ℝ) ^ 2) := by ring
  simpa only [vertexWitness, hscale] using hbound

end UniqueGames.Foundations.PCP.PoweringWitness

end OAI
