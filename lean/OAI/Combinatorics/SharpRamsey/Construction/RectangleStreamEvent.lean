import Mathlib
import OAI.Combinatorics.SharpRamsey.Construction.InitialRectangles
import OAI.Combinatorics.SharpRamsey.Construction.FiniteStreamTail

namespace OAI

section
namespace SharpLogRamsey.RectangleStreamEvent
open Finset Real InitialRectangles FiniteStreamTail
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedRectangleStreamEvent_1 : Fintype (Flag K V) := @Fintype.ofFinite _ (finite_flags (K:=K) (V:=V))
local instance flat_JoinedRectangleStreamEvent_2 : Fintype (Submodule K V) := @Fintype.ofFinite _ (finite_subspaces (K:=K) (V:=V))

def rectangle (W : Submodule K V) : Finset (Flag K V) :=
  univ.filter (IsRectangle W)

lemma rectangle_card {d : ℕ} (hd : 1≤d) (hdim : Module.finrank K V=d+1)
    (W : Submodule K V) : (rectangle W).card≤4*(Nat.card K)^(d-1) := by
  convert card_rectangle_bound hd hdim W using 1
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  rfl

lemma flags_card_pos {d : ℕ} (hd : 1≤d) (hdim : Module.finrank K V=d+1) :
    0<Fintype.card (Flag K V) := by
  have h := card_flags_lower hd hdim
  rw [Nat.card_eq_fintype_card (α:=Flag K V)] at h
  exact lt_of_lt_of_le (pow_pos (Nat.card_pos (α:=K)) _) h

lemma rectangle_probability {d : ℕ} (hd : 1≤d) (hdim : Module.finrank K V=d+1)
    (W : Submodule K V) : probability (rectangle W)≤4/(Nat.card K:ℝ)^d := by
  have hp : 0<(Nat.card K:ℝ) := by exact_mod_cast (show 0<Nat.card K from Nat.card_pos)
  have hf : 0<(Fintype.card (Flag K V):ℝ) := by exact_mod_cast flags_card_pos hd hdim
  have hc : ((rectangle W).card:ℝ)≤4*(Nat.card K:ℝ)^(d-1) := by
    exact_mod_cast rectangle_card hd hdim W
  have hb : (Nat.card K:ℝ)^(2*d-1)≤Fintype.card (Flag K V) := by
    exact_mod_cast (show (Nat.card K)^(2*d-1)≤Fintype.card (Flag K V) by
      simpa only [Nat.card_eq_fintype_card] using card_flags_lower hd hdim)
  unfold probability
  calc
    _ ≤ (4*(Nat.card K:ℝ)^(d-1))/(Nat.card K:ℝ)^(2*d-1) :=
      div_le_div₀ (by positivity) hc (by positivity) hb
    _ = _ := by
      have he : 2*d-1=d+(d-1) := by omega
      rw [he,pow_add]
      field_simp

lemma rectangle_mean {d N : ℕ} (hd : 1≤d) (hdim : Module.finrank K V=d+1)
    (hN : (N:ℝ)≤(Nat.card K:ℝ)^d*log (Nat.card K)) (W : Submodule K V) :
    (N:ℝ)*probability (rectangle W)≤4*log (Nat.card K) := by
  have hp : 0<(Nat.card K:ℝ) := by exact_mod_cast (show 0<Nat.card K from Nat.card_pos)
  calc
    _ ≤ N*(4/(Nat.card K:ℝ)^d) :=
      mul_le_mul_of_nonneg_left (rectangle_probability hd hdim W) (Nat.cast_nonneg _)
    _ ≤ ((Nat.card K:ℝ)^d*log (Nat.card K))*(4/(Nat.card K:ℝ)^d) :=
      mul_le_mul_of_nonneg_right hN (by positivity)
    _ = _ := by field_simp

omit [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] in
lemma union_exponent (q : ℝ) (hq : 0<q) (n : ℕ) :
    q^n*exp (4*log q-(((n:ℝ)+5)/log 2*log q)*log 2)=1/q := by
  have hl : log (2:ℝ)≠0 := ne_of_gt (log_pos (by norm_num))
  have he : 4*log q-(((n:ℝ)+5)/log 2*log q)*log 2=
      -(n:ℝ)*log q-log q := by field_simp; ring
  rw [he]
  have hpow : q^n=exp ((n:ℝ)*log q) := by rw [exp_nat_mul,exp_log hq]
  rw [hpow,←exp_add]
  rw [show (n:ℝ)*log q+(-(n:ℝ)*log q-log q)= -log q by ring,
    exp_neg,exp_log hq,one_div]

theorem simultaneous_rectangle_tail {d N : ℕ} (hd : 1≤d)
    (hdim : Module.finrank K V=d+1)
    (hN : (N:ℝ)≤(Nat.card K:ℝ)^d*log (Nat.card K)) :
    probability (univ.filter (fun z : Fin N→Flag K V=>∃ W : Submodule K V,
      (((d+1)^2:ℕ)+5:ℝ)/log 2*log (Nat.card K)≤hits (rectangle W) z)) ≤
        1/(Nat.card K:ℝ) := by
  have hf := flags_card_pos hd hdim
  let : Nonempty (Flag K V) := Fintype.card_pos_iff.mp hf
  let t : ℝ := (((d+1)^2:ℕ)+5:ℝ)/log 2*log (Nat.card K)
  have hs := simultaneous_tail (rectangle (K:=K) (V:=V)) N t (4*log (Nat.card K))
    (rectangle_mean hd hdim hN)
  have hc : (Fintype.card (Submodule K V):ℝ)≤(Nat.card K:ℝ)^((d+1)^2) := by
    have h := card_subspaces_le (K:=K) (V:=V)
    rw [hdim,Nat.card_eq_fintype_card] at h
    exact_mod_cast h
  calc
    _ ≤ (Fintype.card (Submodule K V):ℝ)*exp (4*log (Nat.card K)-t*log 2) := hs
    _ ≤ (Nat.card K:ℝ)^((d+1)^2)*exp (4*log (Nat.card K)-t*log 2) :=
      mul_le_mul_of_nonneg_right hc (le_of_lt (exp_pos _))
    _ = _ := union_exponent _ (by exact_mod_cast (show 0<Nat.card K from Nat.card_pos)) _

theorem source_length_tail {d : ℕ} (hd : 1≤d) (hdim : Module.finrank K V=d+1) :
    probability (univ.filter (fun z : Fin ⌊(Nat.card K:ℝ)^d*log (Nat.card K)⌋₊→Flag K V=>
      ∃ W : Submodule K V,
        (((d+1)^2:ℕ)+5:ℝ)/log 2*log (Nat.card K)≤hits (rectangle W) z)) ≤
        1/(Nat.card K:ℝ) := by
  apply simultaneous_rectangle_tail hd hdim
  apply Nat.floor_le
  apply mul_nonneg (by positivity)
  apply log_nonneg
  exact_mod_cast (Nat.le_of_lt (Finite.one_lt_card (α:=K)))

omit [Finite K] in

lemma dual_rectangle (U : Submodule K (Module.Dual K V)) (f : Flag K V) :
    IsRectangle U.dualCoannihilator f ↔
      f.dualPoint.submodule≤U ∧ f.point.submodule≤U.dualCoannihilator := by
  simp only [IsRectangle,Subspace.dualCoannihilator_dualAnnihilator_eq,and_comm]

lemma inherited_occupancy {N n : ℕ} (z : Fin N→Flag K V) (e : Fin n↪Fin N)
    (M : ℝ) (h : ∀ W : Submodule K V,(hits (rectangle W) z:ℝ)<M) :
    ∀ W : Submodule K V,(hits (rectangle W) (z∘e):ℝ)<M := by
  intro W
  exact lt_of_le_of_lt (by exact_mod_cast hits_embedding (rectangle W) z e) (h W)

theorem simultaneous_good_probability {d N : ℕ} (hd : 1≤d)
    (hdim : Module.finrank K V=d+1)
    (hN : (N:ℝ)≤(Nat.card K:ℝ)^d*log (Nat.card K)) :
    1-1/(Nat.card K:ℝ) ≤
    probability (univ.filter (fun z : Fin N→Flag K V=>∀ W : Submodule K V,
      (hits (rectangle W) z:ℝ)<(((d+1)^2:ℕ)+5:ℝ)/log 2*log (Nat.card K))) := by
  let : Nonempty (Flag K V) := Fintype.card_pos_iff.mp (flags_card_pos hd hdim)
  let B := univ.filter (fun z : Fin N→Flag K V=>∃ W : Submodule K V,
      (((d+1)^2:ℕ)+5:ℝ)/log 2*log (Nat.card K)≤hits (rectangle W) z)
  have he : Bᶜ=univ.filter (fun z : Fin N→Flag K V=>∀ W : Submodule K V,
      (hits (rectangle W) z:ℝ)<(((d+1)^2:ℕ)+5:ℝ)/log 2*log (Nat.card K)) := by
    ext z
    simp only [B,mem_compl,mem_filter,mem_univ,true_and,not_exists,not_le]
  rw [←he]
  have hc : probability Bᶜ=1-probability B := by
    convert probability_compl B using 1
    congr 1
    ext z
    simp
  rw [hc]
  exact sub_le_sub_left (simultaneous_rectangle_tail hd hdim hN) 1

theorem source_good_probability {d : ℕ} (hd : 1≤d) (hdim : Module.finrank K V=d+1) :
    (1:ℝ)/2 ≤
    probability (univ.filter (fun z : Fin ⌊(Nat.card K:ℝ)^d*log (Nat.card K)⌋₊→Flag K V=>
      ∀ W : Submodule K V,
        (hits (rectangle W) z:ℝ)<(((d+1)^2:ℕ)+5:ℝ)/log 2*log (Nat.card K))) := by
  have hq : 2≤(Nat.card K:ℝ) := by exact_mod_cast (Finite.one_lt_card (α:=K))
  have hp : 0<(Nat.card K:ℝ) := by linarith
  have hh : 1/(Nat.card K:ℝ)≤1/2 := (div_le_iff₀ hp).mpr (by linarith)
  apply (show (1:ℝ)/2≤1-1/(Nat.card K:ℝ) by linarith).trans
  apply simultaneous_good_probability hd hdim
  exact Nat.floor_le (mul_nonneg (by positivity) (log_nonneg (by linarith)))

end
end SharpLogRamsey.RectangleStreamEvent

end

end OAI
