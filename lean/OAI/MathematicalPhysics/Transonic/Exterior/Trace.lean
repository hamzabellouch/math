import OAI.MathematicalPhysics.Transonic.Exterior.Conv
import OAI.MathematicalPhysics.Transonic.Exterior.Interval

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorJet
open PowerSeries Finset FixedInterval

lemma enclosed_pos {Q : ℤ} (hQ : 0<Q) {b : Box} {x : ℝ}
    (hx : Holds Q b x) (hb : 0<b.center-b.radius) : 0<x := by
  have h := (abs_le.mp hx).1
  have hQ' : (0:ℝ)<Q := by exact_mod_cast hQ
  have hb' : (0:ℝ)<(b.center:ℝ)-b.radius := by exact_mod_cast hb
  nlinarith

def oneBox (Q : ℤ) : Box := ⟨Q,0⟩
lemma holds_oneBox (Q : ℤ) : Holds Q (oneBox Q) 1 := by simp [Holds,oneBox]

def divBox (Q : ℤ) (a b : Box) : Box := mul Q a (inv Q b)
def pairBox (Q : ℤ) (b r : ℕ → Box) (i j : ℕ) : Box := mul Q (b (min i j)) (r (max i j))
def squareBox (Q : ℤ) (D : ℕ) (b r : ℕ → Box) (n : ℕ) : Box :=
  sumBox D 1 n fun i => pairBox Q b r i (n-i)
def squareRestBox (Q : ℤ) (D : ℕ) (b r : ℕ → Box) (n : ℕ) : Box :=
  sumBox D 2 n fun i => pairBox Q b r i (n+1-i)
def power2Box (Q : ℤ) (sc r : ℕ → Box) (n : ℕ) : Box :=
  if n<2 then zero else mul Q (sc n) (r (n-1))
def power3Box (Q : ℤ) (D : ℕ) (b r sc : ℕ → Box) (n : ℕ) : Box :=
  sumBox D 1 (n-1) fun i => mul Q (pairBox Q b r i (n-i-1)) (sc (n-i))
def power4Box (Q : ℤ) (D : ℕ) (b r sc : ℕ → Box) (n : ℕ) : Box :=
  sumBox D 2 (n-1) fun i => mul Q (mul Q (pairBox Q b r (i-1) (n-i-1)) (sc i)) (sc (n-i))

lemma relative_enclosed {Q : ℤ} (hQ : 0<Q) (b : ℕ → ℝ) (rat rel : ℕ → Box)
    (N : ℕ) (hN : b N≠0)
    (hr : ∀ j, 2≤j → j≤N → Holds Q (rat j) (b j/b (j-1)))
    (hpos : ∀ j, 2≤j → j≤N → 0<(rat j).center-(rat j).radius)
    (hb : ∀ j, 1≤j → j≤N → b j≠0)
    (hself : rel N=oneBox Q)
    (hstep : ∀ j, 1≤j → j<N → rel j=divBox Q (rel (j+1)) (rat (j+1))) :
    ∀ j, 1≤j → j≤N → Holds Q (rel j) (relative b N j) := by
  intro j hj hjN
  induction h : N-j using Nat.strong_induction_on generalizing j with
  | h d ih =>
    by_cases he : j=N
    · subst j;rw [relative_self hN,hself];exact holds_oneBox Q
    · have hjlt : j<N := by omega
      have hnext := ih (N-(j+1)) (by omega) (j+1) (by omega) (by omega) rfl
      rw [hstep j hj hjlt,relative_step N j (hb j hj hjN) (hb (j+1) (by omega) (by omega))]
      apply holds_div hQ hnext
      · simpa only [Nat.add_sub_cancel] using hr (j+1) (by omega) (by omega)
      · exact hpos (j+1) (by omega) (by omega)

lemma pair_enclosed {Q : ℤ} (hQ : 0<Q) (b r : ℕ → Box) (w : Series) (N M : ℕ)
    (hb : ∀ j, 1≤j → j≤M → Holds Q (b j) (coeff j w))
    (hr : ∀ j, 1≤j → j≤N → Holds Q (r j) (relative (fun i => coeff i w) N j))
    (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hij : min i j ≤ M) (hij' : max i j ≤ N) :
    Holds Q (pairBox Q b r i j) (pairValue (fun i => coeff i w) N i j) :=
  holds_mul hQ (hb _ (le_min hi hj) hij) (hr _ (le_trans hi (le_max_left _ _)) hij')

lemma square_enclosed {Q : ℤ} (hQ : 0<Q) (D n : ℕ) (hd : n≤2^D)
    (b r : ℕ → Box) (w : Series) (hw : coeff 0 w=0)
    (hb : ∀ j, 1≤j → j<n → Holds Q (b j) (coeff j w))
    (hr : ∀ j, 1≤j → j<n → Holds Q (r j) (relative (fun i => coeff i w) (n-1) j)) :
    Holds Q (squareBox Q D b r n) (squareRatio w n) := by
  rw [squareRatio_sum w hw]
  apply holds_sumBox D 1 n _ _ hd
  intro i hi hi'
  apply pair_enclosed hQ b r w (n-1) (n-1)
  · intro j hj hj';exact hb j hj (by omega)
  · intro j hj hj';exact hr j hj (by omega)
  all_goals omega

lemma squareRest_enclosed {Q : ℤ} (hQ : 0<Q) (D n : ℕ) (hd : n≤2^D)
    (b r : ℕ → Box) (w : Series)
    (hb : ∀ j, 1≤j → j<n → Holds Q (b j) (coeff j w))
    (hr : ∀ j, 1≤j → j<n → Holds Q (r j) (relative (fun i => coeff i w) (n-1) j)) :
    Holds Q (squareRestBox Q D b r n) (squareRRatio w n) := by
  rw [squareRRatio_sum]
  apply holds_sumBox D 2 n _ _ hd
  intro i hi hi'
  apply pair_enclosed hQ b r w (n-1) (n-1)
  · intro j hj hj';exact hb j hj (by omega)
  · intro j hj hj';exact hr j hj (by omega)
  all_goals omega

lemma power2_enclosed {Q : ℤ} (hQ : 0<Q) (sc r : ℕ → Box) (w : Series)
    (hw : coeff 0 w=0) (N M n : ℕ) (hn : n≤M) (hn' : n-1≤N)
    (hb : ∀ j, 1≤j → j≤N → coeff j w≠0)
    (hsc : ∀ j, 2≤j → j≤M → Holds Q (sc j) (squareRatio w j))
    (hr : ∀ j, 1≤j → j≤N → Holds Q (r j) (relative (fun i => coeff i w) N j)) :
    Holds Q (power2Box Q sc r n) (powerRatio w N 2 n) := by
  unfold power2Box
  split_ifs with h
  · rw [powerRatio_low hw h];exact holds_zero Q
  · rw [powerRatio_square (hb (n-1) (by omega) hn')]
    exact holds_mul hQ (hsc n (by omega) hn) (hr (n-1) (by omega) hn')

lemma power3_enclosed {Q : ℤ} (hQ : 0<Q) (D : ℕ) (b r sc : ℕ → Box) (w : Series)
    (hw : coeff 0 w=0) (N M n : ℕ) (hn : n-1≤M) (hn' : n-2≤N) (hd : n-1≤2^D)
    (hb0 : ∀ j, 1≤j → j≤N → coeff j w≠0)
    (hb : ∀ j, 1≤j → j≤N → Holds Q (b j) (coeff j w))
    (hsc : ∀ j, 2≤j → j≤M → Holds Q (sc j) (squareRatio w j))
    (hr : ∀ j, 1≤j → j≤N → Holds Q (r j) (relative (fun i => coeff i w) N j)) :
    Holds Q (power3Box Q D b r sc n) (powerRatio w N 3 n) := by
  rw [powerRatio_cube w hw N n (fun j hj hj' => hb0 j hj (by omega))]
  apply holds_sumBox D 1 (n-1) _ _ hd
  intro i hi hi'
  apply holds_mul hQ
  · apply pair_enclosed hQ b r w N N hb hr <;> omega
  · exact hsc (n-i) (by omega) (by omega)

lemma power4_enclosed {Q : ℤ} (hQ : 0<Q) (D : ℕ) (b r sc : ℕ → Box) (w : Series)
    (hw : coeff 0 w=0) (N M n : ℕ) (hn : n-2≤M) (hn' : n-3≤N) (hd : n-1≤2^D)
    (hb0 : ∀ j, 1≤j → j≤N → coeff j w≠0)
    (hb : ∀ j, 1≤j → j≤N → Holds Q (b j) (coeff j w))
    (hsc : ∀ j, 2≤j → j≤M → Holds Q (sc j) (squareRatio w j))
    (hr : ∀ j, 1≤j → j≤N → Holds Q (r j) (relative (fun i => coeff i w) N j)) :
    Holds Q (power4Box Q D b r sc n) (powerRatio w N 4 n) := by
  rw [powerRatio_fourth w hw N n (fun j hj hj' => hb0 j hj (by omega))]
  apply holds_sumBox D 2 (n-1) _ _ hd
  intro i hi hi'
  apply holds_mul hQ
  · apply holds_mul hQ
    · apply pair_enclosed hQ b r w N N hb hr <;> omega
    · exact hsc i (by omega) (by omega)
  · exact hsc (n-i) (by omega) (by omega)

end SepticProfile.ExteriorJet

end
end

end OAI
