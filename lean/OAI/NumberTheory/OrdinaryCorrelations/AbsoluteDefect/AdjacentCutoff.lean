import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.BinQ

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace OrdinaryChainScales
open OrdinaryNarrowGrid
attribute [local irreducible] E F mesh binQ binStart binWidth binLog amplifier

lemma adjacent_cutoff {g : ℕ→ℕ} (hg : StrictMono g) {X : ℕ} (h0 : g 0≤X) :
    ∃j, g j≤X ∧ X<g (j+1) := by
  have hex : ∃j,X<g j := ⟨X+1,lt_of_lt_of_le (by omega : X<X+1) (hg.id_le (X+1))⟩
  let n := Nat.find hex
  have hgt : X<g n := Nat.find_spec hex
  have hn : 0<n := by
    by_contra hh
    have hz : n=0 := by omega
    rw [hz] at hgt
    omega
  refine ⟨n-1,?_,?_⟩
  · exact le_of_not_gt (Nat.find_min hex (by omega : n-1<n))
  · simpa only [Nat.sub_add_cancel hn] using hgt

lemma terminal_index {B s R X : ℕ} (hR : 0<R)
    (hX : (2^(F B s 0))^(64*R)≤X) :
    ∃j,(2^(F B s j))^(64*R)≤X ∧ X<(2^(F B s (j+1)))^(64*R) := by
  apply adjacent_cutoff _ hX
  intro i j hij
  apply Nat.pow_lt_pow_left (Nat.pow_lt_pow_right (by omega) (F_mono B s hij)) (by omega)

lemma terminal_moment_lower {R N Q X : ℕ} (hR : 0<R) (hQ : 2≤Q)
    (hN : 1≤N) (hNQ : N≤Q) (hX : Q^(64*R)≤X) :
    4*R≤Nat.log (2*N) X := by
  have hXp : 0<X := lt_of_lt_of_le (by positivity : 0<Q^(64*R)) hX
  apply (Nat.le_log_iff_pow_le (by omega) hXp.ne').mpr
  calc
    (2*N)^(4*R) ≤ (Q^2)^(4*R) := Nat.pow_le_pow_left (by nlinarith) _
    _ = Q^(8*R) := by rw [←pow_mul]; congr 1; omega
    _ ≤ Q^(64*R) := Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ X := hX

lemma terminal_moment_upper {B s j R N X : ℕ} (hX : 0<X)
    (hN : 2^(E B s j)≤N) (hQ : X<(2^(F B s (j+1)))^(64*R)) :
    Nat.log (2*N) X<64*R*2^(3*j+2*s+22) := by
  have hlo := Nat.pow_log_le_self (2*N) hX.ne'
  have he : 0<E B s j := E_pos B s j
  have hpow : 2^(E B s j*Nat.log (2*N) X)<2^(F B s (j+1)*(64*R)) := by
    rw [pow_mul,pow_mul]
    exact (Nat.pow_le_pow_left (by omega : 2^(E B s j)≤2*N) _).trans_lt (hlo.trans_lt hQ)
  have hlt := (Nat.pow_lt_pow_iff_right (by omega : 1<(2:ℕ))).mp hpow
  rw [next_F] at hlt
  nlinarith

lemma terminal_square_absorption {B H s j K Kr k R : ℕ}
    (hB : H+4*s+2*Kr+K+70≤B) (hR : 64*R≤2^Kr)
    (hk : k<64*R*2^(3*j+2*s+22)) :
    2^K*(k+1)^2≤ mesh B H s j := by
  have hkp : k+1≤2^(Kr+3*j+2*s+22) := by
    have hh := Nat.mul_le_mul_right (2^(3*j+2*s+22)) hR
    rw [←pow_add] at hh
    have he : Kr+(3*j+2*s+22)=Kr+3*j+2*s+22 := by omega
    rw [he] at hh
    omega
  calc
    _ ≤ 2^K*(2^(Kr+3*j+2*s+22))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hkp _)
    _ = 2^(K+(Kr+3*j+2*s+22)*2) := by rw [←pow_mul,←pow_add]
    _ ≤ mesh B H s j := by
      unfold mesh
      apply Nat.pow_le_pow_right (by omega)
      have he : B-H-10+H+10=B := by omega
      nlinarith

lemma terminal_grid_card {B H s j R X : ℕ} (hB : 2*H+s+30≤B)
    (hX : (2^(F B s j))^(64*R)≤X) :
    (grid (binQ B H s j) (binStart B H s j) (binWidth B s j)).card^R≤X := by
  have hc := bin_card_bound (B:=B) (H:=H) (s:=s) (j:=j) hB
  have hm := (mesh_le_E B H s j (by omega)).trans (E_le_F B s j)
  calc
    _ ≤ (2^(2*mesh B H s j))^R := Nat.pow_le_pow_left hc _
    _ = 2^((2*mesh B H s j)*R) := (pow_mul _ _ _).symm
    _ ≤ 2^((F B s j)*(64*R)) := Nat.pow_le_pow_right (by omega) (by nlinarith)
    _ = (2^(F B s j))^(64*R) := pow_mul _ _ _
    _ ≤ X := hX

end OrdinaryChainScales

end

end OAI
