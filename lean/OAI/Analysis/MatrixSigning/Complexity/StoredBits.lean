import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.NaturalPolynomial
import OAI.Analysis.MatrixSigning.Optimization.Transition
import OAI.Analysis.MatrixSigning.Optimization.UpperIndex
import OAI.Analysis.MatrixSigning.Potential.PenaltyParameter
import OAI.Analysis.MatrixSigning.Complexity.BitSupport
import OAI.Analysis.MatrixSigning.Complexity.RationalGridBits

namespace OAI

namespace CurrentKS.ScheduleBits
open CurrentKS.RationalBits

abbrev Args := Fin 4 → ℚ
private def eps (x:Args) := x 2/x 0
private def strip (x:Args) := (x 3)^2/x 2
private def movement (x:Args) : ℚ :=
  let s₀ := eps x/40000
  let J := 1+(3*x 1)^2/s₀
  let E₀ := 2*J^2*(1+3*x 1)^2
  max 1 (max (48*E₀/23) (4*(1+9*(x 1)^2)))
private def coarse (x:Args) : ℚ :=
  200+(x 0+1)+|eps x|+(200/eps x)*(x 0+1)+200*(x 0+1)+
    ((x 0+1)+x 1)+384*x 1*(1+800/(strip x)^3)
private def jacobian (x:Args) : ℚ := 10^18*(x 0+1)*(1+(eps x)⁻¹)^4
private def derivative (x:Args) : ℚ := 300*(coarse x)^5
def second (x:Args) : ℚ :=
  (1+|eps x| *(2*(x 0+1)))*(jacobian x*derivative x*(1+jacobian x*derivative x)^2)
private def third (x:Args) : ℚ :=
  (1+|eps x| *(2*(x 0+1)))*(jacobian x*derivative x*
    ((1+jacobian x*derivative x)^3+3*(1+jacobian x*derivative x)*
      (jacobian x*derivative x*(1+jacobian x*derivative x)^2)))
private def curvature (x:Args) : ℚ :=
  1+second x+third x+|x 3| *x 1*(1+800/(strip x)^3)
def threshold (x:Args) : ℚ := x 3/(512*(movement x)^2)
def step (x:Args) : ℚ := min (strip x/4) (min (threshold x/(4*curvature x)) (1/4))
private def mesh (x:Args) : ℚ := step x*threshold x/(4096*curvature x*x 1)

syntax "bit_linear" : tactic
macro_rules
  | `(tactic| bit_linear) => `(tactic|
      with_reducible first
      | assumption
      | exact LinearBits.coordinate _
      | exact LinearBits.constant _
      | apply LinearBits.add <;> bit_linear
      | apply LinearBits.mul <;> bit_linear
      | apply LinearBits.div <;> bit_linear
      | apply LinearBits.inv <;> bit_linear
      | apply LinearBits.pow <;> bit_linear
      | apply LinearBits.abs <;> bit_linear
      | apply LinearBits.min <;> bit_linear
      | apply LinearBits.max <;> bit_linear)

private lemma eps_bits : LinearBits eps := by unfold eps;bit_linear
private lemma strip_bits : LinearBits strip := by unfold strip;bit_linear
private lemma movement_bits : LinearBits movement := by
  have he := eps_bits
  unfold movement
  dsimp only
  bit_linear
private lemma coarse_bits : LinearBits coarse := by
  have he := eps_bits
  have hs := strip_bits
  unfold coarse
  bit_linear
private lemma jacobian_bits : LinearBits jacobian := by
  have he := eps_bits
  unfold jacobian
  bit_linear
private lemma derivative_bits : LinearBits derivative := by
  have hc := coarse_bits
  unfold derivative
  bit_linear
private lemma second_bits : LinearBits second := by
  have he := eps_bits
  have hj := jacobian_bits
  have hd := derivative_bits
  unfold second
  bit_linear
private lemma third_bits : LinearBits third := by
  have he := eps_bits
  have hj := jacobian_bits
  have hd := derivative_bits
  unfold third
  bit_linear
private lemma curvature_bits : LinearBits curvature := by
  have hs := strip_bits
  have h2 := second_bits
  have h3 := third_bits
  unfold curvature
  bit_linear
private lemma threshold_bits : LinearBits threshold := by
  have hm := movement_bits
  unfold threshold
  bit_linear
private lemma step_bits : LinearBits step := by
  have hs := strip_bits
  have ht := threshold_bits
  have hc := curvature_bits
  unfold step
  bit_linear
private lemma mesh_bits : LinearBits mesh := by
  have hs := step_bits
  have ht := threshold_bits
  have hc := curvature_bits
  unfold mesh
  bit_linear

private def args (d n : ℕ) (ν lam:ℚ) : Args := ![d,n,ν,lam]
lemma step_eq (d n:ℕ) (ν lam:ℚ) :
    step (args d n ν lam)=(CurrentKS.Schedule.parameters d n ν lam).s := rfl
private lemma mesh_eq (d n:ℕ) (ν lam:ℚ) :
    mesh (args d n ν lam)=(CurrentKS.Schedule.parameters d n ν lam).ρ := rfl

theorem schedule_parts_linear : ∃ C:ℕ, 0<C ∧ ∀ (d n : ℕ) (ν lam : ℚ) (b : ℕ),
    Parts b (d:ℚ) → Parts b (n:ℚ) → Parts b ν → Parts b lam →
    Parts (C*(b+1)) (CurrentKS.Schedule.parameters d n ν lam).s ∧
      Parts (C*(b+1)) (CurrentKS.Schedule.parameters d n ν lam).ρ := by
  obtain ⟨C,hC,hstep⟩ := step_bits
  obtain ⟨D,hD,hmesh⟩ := mesh_bits
  refine ⟨C+D,by omega,?_⟩
  intro d n ν lam b hd hn hν hl
  have hx : ∀i,Parts b (args d n ν lam i) := by
    intro i
    fin_cases i <;> simp only [args] <;> assumption
  have hs := (hstep b (args d n ν lam) hx).mono (show C*(b+1)≤(C+D)*(b+1) by nlinarith)
  have hm := (hmesh b (args d n ν lam) hx).mono (show D*(b+1)≤(C+D)*(b+1) by nlinarith)
  rw [step_eq] at hs
  rw [mesh_eq] at hm
  exact ⟨hs,hm⟩
end CurrentKS.ScheduleBits
namespace CurrentKS.RationalBits
open CurrentKS.RationalGridSize

lemma Parts.natCast {b n : ℕ} (hn : n ≤ 2^b) : Parts b (n:ℚ) := by
  constructor
  · simpa only [Rat.num_natCast,Int.natAbs_natCast] using hn
  · simpa only [Rat.den_natCast] using Nat.one_le_two_pow

lemma natCast_parts (n : ℕ) : Parts n.size (n:ℚ) := Parts.natCast (Nat.lt_size_self n).le

end CurrentKS.RationalBits

namespace CurrentKS.RationalGridSize

lemma Grid.mono {D E : ℕ} {q : ℚ} (hq : Grid D q) (hDE : D ∣ E) : Grid E q := hq.trans hDE

lemma Grid.half {D : ℕ} {q : ℚ} (hq : Grid D q) : Grid (D*2) (q/2) := by
  rw [div_eq_mul_inv]
  apply (Rat.mul_den_dvd q ((2:ℚ)⁻¹)).trans
  norm_num
  exact Nat.mul_dvd_mul_right hq 2

end CurrentKS.RationalGridSize

namespace CurrentKS.RationalRoot
open CurrentKS.RationalGridSize CurrentKS.RationalBits

lemma squareInterval_grid (q : ℚ) (k : ℕ) :
    Grid (2^k) (squareInterval q k).1 ∧ Grid (2^k) (squareInterval q k).2 := by
  induction k with
  | zero => exact ⟨Grid.zero _,Grid.one _⟩
  | succ k ih =>
    have hm := (ih.1.add ih.2).half
    have hlow := ih.1.mono (dvd_mul_right (2^k) 2)
    have hupp := ih.2.mono (dvd_mul_right (2^k) 2)
    simp only [squareInterval]
    split
    · simpa only [pow_succ] using And.intro hm hupp
    · simpa only [pow_succ] using And.intro hlow hm

lemma squareInterval_cube (q : ℚ) (k : ℕ) :
    0 ≤ (squareInterval q k).1 ∧ (squareInterval q k).1 ≤ (squareInterval q k).2 ∧
      (squareInterval q k).2 ≤ 1 := by
  induction k with
  | zero => norm_num [squareInterval]
  | succ k ih =>
    simp only [squareInterval]
    split <;> dsimp only <;> constructor
    · linarith [ih.1,ih.2.1]
    · exact ⟨by linarith [ih.2.1],ih.2.2⟩
    · exact ih.1
    · constructor <;> linarith [ih.2.1,ih.2.2]

lemma upperSqrt_parts (q δ : ℚ) : Parts δ.den.size (upperSqrt q δ) := by
  have hg := (squareInterval_grid q δ.den.size).2
  have hc := squareInterval_cube q δ.den.size
  have ha : |upperSqrt q δ| ≤ 1 := by
    change |(squareInterval q δ.den.size).2| ≤ 1
    rw [abs_of_nonneg (hc.1.trans hc.2.1)]
    exact hc.2.2
  exact coordinate_size_bound (by positivity) hg ha
end CurrentKS.RationalRoot

namespace CurrentKS.RationalGrid
open CurrentKS.RationalBits

lemma upper_parts (den : ℕ) (test : ℚ → Bool) : Parts (2*den.size) (upper den test) := by
  have hn : Parts den.size (upperIndex den test den:ℚ) :=
    Parts.natCast ((upperIndex_le den test den).trans (Nat.lt_size_self den).le)
  simp only [two_mul]
  exact hn.div (natCast_parts den)
end CurrentKS.RationalGrid

namespace CurrentKS.RationalFace
open CurrentKS.RationalBits CurrentKS.RationalRoot CurrentKS.RationalSDP CurrentKS.Schedule
open scoped BigOperators

variable {d N : ℕ}

def baseBits (d N : ℕ) : ℕ := d.size+N.size+2*(1000*N*d^2).size+1+(200*N).size

lemma variance_parts (coords : Fin N → Fin d × Fin d → ℚ) :
    Parts (2*(1000*N*d^2).size) (varianceQuery coords) :=
  CurrentKS.RationalGrid.upper_parts _ _

lemma penalty_parts (ν : ℚ) (N b : ℕ) (hν : Parts b ν) :
    Parts (b+1+(200*N).size) (penaltyParameter N ν) := by
  have hd : ν.den.size ≤ b+1 := by simpa only [Nat.size_pow] using Nat.size_le_size hν.2
  have hu := (upperSqrt_parts ν ν).mono hd
  have hc : Parts (200*N).size ((200:ℚ)*N) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using natCast_parts (200*N)
  exact hu.div hc

lemma base_parts (coords : Fin N → Fin d × Fin d → ℚ) (n : ℕ) (hn : n ≤ N) :
    Parts (baseBits d N) (d:ℚ) ∧ Parts (baseBits d N) (n:ℚ) ∧
      Parts (baseBits d N) (varianceQuery coords) ∧
      Parts (baseBits d N) (penaltyParameter N (varianceQuery coords)) := by
  have hν := variance_parts coords
  have hlam := penalty_parts (varianceQuery coords) N _ hν
  refine ⟨(natCast_parts d).mono ?_,(natCast_parts n).mono ?_,hν.mono ?_,hlam.mono ?_⟩
  all_goals dsimp only [baseBits]
  · omega
  · have h := Nat.size_le_size hn;omega
  · omega
  · omega

end CurrentKS.RationalFace
namespace CurrentKS.RationalRoot
open CurrentKS.RationalGridSize

variable {N : ℕ}

lemma roundMesh_grid {D : ℕ} {ρ : ℚ} (hρ : Grid D ρ) (v : Fin N → ℚ) :
    ∀ i,Grid D (roundMesh ρ v i) :=
  fun i => hρ.mul_integer (nearest (v i/ρ))

lemma computedCurvature_grid {D : ℕ} (H : Matrix (Fin N) (Fin N) ℚ)
    (a M s ρ : ℚ) (hρ : Grid D ρ) (q : Fin N → ℚ)
    (hq : computedCurvature H a M s ρ=some q) : ∀ i,Grid D (q i) := by
  unfold computedCurvature at hq
  cases he : negativeDirection (shiftedHessian H a) (a/(4096*M)) with
  | none => simp only [he,Option.map_none] at hq;cases hq
  | some w =>
    simp only [he,Option.map_some,Option.some.injEq] at hq
    subst q
    exact roundMesh_grid hρ _

end CurrentKS.RationalRoot

namespace CurrentKS.Difference
open CurrentKS.RationalGridSize CurrentKS.RationalRoot

variable {N : ℕ}

lemma gradientStep_grid [NeZero N] {D : ℕ} (s : ℚ) (g : Fin N → ℚ)
    (hs : Grid D s) : ∀ i,Grid D ((s • rationalGradientDirection g) i) := by
  intro i
  simp only [rationalGradientDirection,Pi.smul_apply,smul_eq_mul,Pi.single_apply]
  split_ifs <;> simp only [mul_neg,mul_one,mul_zero]
  all_goals first | exact hs | exact hs.neg | exact Grid.zero D

lemma interiorCandidates_grid [NeZero N] {D : ℕ}
    (query : (Fin N → ℚ) → ℚ) (x : Fin N → ℚ) (h a M s ρ : ℚ)
    (hx : ∀ i,Grid D (x i)) (hs : Grid D s) (hρ : Grid D ρ) :
    ∀ y∈interiorCandidates query x h a M s ρ,∀ i,Grid D (y i) := by
  intro y hy
  simp only [interiorCandidates,List.mem_cons] at hy
  rcases hy with rfl|hy
  · exact fun i => (hx i).add (gradientStep_grid s _ hs i)
  · cases he : computedCurvature (stencilHessian query x h) a M s ρ with
    | none => simp only [he,List.not_mem_nil] at hy
    | some q =>
      have hq := computedCurvature_grid _ a M s ρ hρ q he
      simp only [he,List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl|rfl
      · exact fun i => (hx i).add (hq i)
      · exact fun i => (hx i).sub (hq i)

lemma endpointCandidates_grid {D : ℕ} (x : Fin N → ℚ) (hx : ∀ i,Grid D (x i)) :
    ∀ y∈endpointCandidates x,∀ i,Grid D (y i) := by
  intro y hy j
  obtain ⟨i,_,hy⟩ := List.mem_flatMap.mp hy
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
  rcases hy with rfl|rfl
  all_goals
    by_cases hji : j=i
    · subst j;simp only [Function.update_self]
      exact (Grid.one D).neg
    · simpa only [Function.update_of_ne hji] using hx j

lemma allCandidates_grid [NeZero N] {D : ℕ}
    (query : (Fin N → ℚ) → ℚ) (x : Fin N → ℚ) (h a M s ρ : ℚ)
    (hx : ∀ i,Grid D (x i)) (hs : Grid D s) (hρ : Grid D ρ) :
    ∀ y∈allCandidates query x h a M s ρ,∀ i,Grid D (y i) := by
  intro y hy
  rcases List.mem_append.mp hy with he|hi
  · exact endpointCandidates_grid x hx y he
  · exact interiorCandidates_grid query x h a M s ρ hx hs hρ y hi

end CurrentKS.Difference

namespace CurrentKS.RationalFace

section
open CurrentKS.RationalGridSize CurrentKS.Schedule CurrentKS.Descent CurrentKS.Difference
open scoped BigOperators

variable {d N n : ℕ}

def meshDenominator (d N : ℕ) (ν lam : ℚ) : ℕ :=
  ∏ n ∈ Finset.range (N+1), (parameters d n ν lam).s.den*(parameters d n ν lam).ρ.den

lemma meshDenominator_pos (d N : ℕ) (ν lam : ℚ) : 0 < meshDenominator d N ν lam := by
  apply Finset.prod_pos
  intro n _
  exact Nat.mul_pos (Rat.den_pos _) (Rat.den_pos _)

lemma schedule_grid (d N n : ℕ) (ν lam : ℚ) (hn : n ≤ N) :
    Grid (meshDenominator d N ν lam) (parameters d n ν lam).s ∧
    Grid (meshDenominator d N ν lam) (parameters d n ν lam).ρ := by
  have hprod := Finset.dvd_prod_of_mem
    (fun n => (parameters d n ν lam).s.den*(parameters d n ν lam).ρ.den)
    (Finset.mem_range.mpr (show n < N+1 by omega))
  exact ⟨(dvd_mul_right _ _).trans hprod,(dvd_mul_left _ _).trans hprod⟩

lemma extend_grid {D : ℕ} (e : Fin n → Fin N) (x : Fin N → ℚ) (y : Fin n → ℚ)
    (hx : ∀ i,Grid D (x i)) (hy : ∀ i,Grid D (y i)) : ∀ i,Grid D (extend e x y i) := by
  intro i
  unfold extend
  cases lookup e i with
  | none => exact hx i
  | some j => exact hy j

lemma freezeOne_grid {D : ℕ} (σ : ℚ) (x : Fin N → ℚ) (hx : ∀ i,Grid D (x i))
    (i : Fin N) : ∀ j,Grid D (freezeOne σ x i j) := by
  intro j
  unfold freezeOne
  split_ifs
  · by_cases hji : j=i
    · subst j
      simp only [Function.update_self,nearestEndpoint]
      split_ifs
      · exact Grid.one D
      · exact (Grid.one D).neg
    · simpa only [Function.update_of_ne hji] using hx j
  · exact hx j

lemma freezeList_grid {D : ℕ} (σ : ℚ) (x : Fin N → ℚ) (hx : ∀ i,Grid D (x i))
    (l : List (Fin N)) : ∀ i,Grid D (freezeList σ x l i) := by
  induction l generalizing x with
  | nil => exact hx
  | cons i l ih => exact ih _ (freezeOne_grid σ x hx i)

lemma faceChoice_grid (coords : Fin N → Fin d × Fin d → ℚ) (base : Fin N → ℚ)
    (ν lam : ℚ) [NeZero (activeIndices base).length]
    (hx : ∀ i,Grid (meshDenominator d N ν lam) (base i)) :
    ∀ i,Grid (meshDenominator d N ν lam) (faceChoice coords base ν lam i) := by
  have hm := select_mem (faceScore coords base ν lam) (faceState base)
    (faceCandidates coords base ν lam)
  have hp := schedule_grid d N (activeIndices base).length ν lam (activeIndices_length_le base)
  rcases List.mem_cons.mp hm with h|h
  · simp only [faceChoice,h]
    exact (fun i => hx (activeIndex base i))
  · exact allCandidates_grid _ _ _ _ _ _ _ (fun i => hx (activeIndex base i)) hp.1 hp.2 _ h

lemma transition_grid (coords : Fin N → Fin d × Fin d → ℚ) (ν lam : ℚ)
    (x y : Fin N → ℚ) (hx : ∀ i,Grid (meshDenominator d N ν lam) (x i))
    (hs : transition coords ν lam x=some y) :
    ∀ i,Grid (meshDenominator d N ν lam) (y i) := by
  by_cases hn : (activeIndices x).length=0
  · simp only [transition,dite_eq_left hn] at hs;cases hs
  · let : NeZero (activeIndices x).length := ⟨hn⟩
    have he : y=freezeAll (lam^2/ν) (extend (activeIndex x) x (faceChoice coords x ν lam)) := by
      simpa only [transition,dite_eq_right hn,Option.some.injEq] using hs.symm
    rw [he]
    exact freezeList_grid _ _ (extend_grid _ _ _ hx (faceChoice_grid coords x ν lam hx)) _

theorem rationalRun_grid (coords : Fin N → Fin d × Fin d → ℚ) (ν lam : ℚ) :
    ∀ i,Grid (meshDenominator d N ν lam) (rationalRun coords ν lam i) := by
  apply run_invariant (transition coords ν lam) (fun x => ∀ i,Grid (meshDenominator d N ν lam) (x i))
    (fun x y hx hs => transition_grid coords ν lam x y hx hs)
  exact freezeList_grid _ _ (fun _ => Grid.zero _) _

end
open CurrentKS.RationalBits CurrentKS.RationalGridSize CurrentKS.ScheduleBits
open CurrentKS.Schedule CurrentKS.RationalSDP CurrentKS.Descent
open KS.W23
open scoped BigOperators

variable {d N : ℕ}

private def baseBitsP : NaturalPolynomial :=
  NaturalPolynomial.variable+NaturalPolynomial.variable+
    2*(1000*NaturalPolynomial.variable*NaturalPolynomial.variable^2)+1+200*NaturalPolynomial.variable
private def meshBitsP (C : ℕ) : NaturalPolynomial :=
  1+(NaturalPolynomial.variable+1)*(2*(NaturalPolynomial.constant C*(baseBitsP+1)+1))

def storedBitsP (C : ℕ) : NaturalPolynomial := 2*meshBitsP C

lemma baseBits_le (B : ℕ) (hd : d ≤ B) (hN : N ≤ B) : baseBits d N ≤ baseBitsP.eval B := by
  have hs (n : ℕ) : n.size ≤ n := Nat.size_le.mpr n.lt_two_pow_self
  change d.size+N.size+2*(1000*N*d^2).size+1+(200*N).size ≤
    B+B+2*(1000*B*B^2)+1+200*B
  apply Nat.add_le_add
  · apply Nat.add_le_add_right
    apply Nat.add_le_add
    · exact Nat.add_le_add ((hs d).trans hd) ((hs N).trans hN)
    · apply Nat.mul_le_mul_left
      apply (hs _).trans
      gcongr
  · exact (hs _).trans (Nat.mul_le_mul_left _ hN)

lemma mesh_bits_bound (C : ℕ) (b : ℕ) (ν lam : ℚ)
    (hs : ∀ n ≤ N, Parts (C*(b+1)) (parameters d n ν lam).s ∧
      Parts (C*(b+1)) (parameters d n ν lam).ρ) :
    (meshDenominator d N ν lam).size ≤ 1+(N+1)*(2*(C*(b+1)+1)) := by
  apply (size_prod_le (Finset.range (N+1))
    (fun n => (parameters d n ν lam).s.den*(parameters d n ν lam).ρ.den)).trans
  apply Nat.add_le_add_left
  calc
    ∑ n∈Finset.range (N+1),((parameters d n ν lam).s.den*(parameters d n ν lam).ρ.den).size
        ≤ ∑ _n∈Finset.range (N+1),2*(C*(b+1)+1) := by
      apply Finset.sum_le_sum
      intro n hn
      have hh := hs n (by have := Finset.mem_range.mp hn;omega)
      have h1 : (parameters d n ν lam).s.den.size ≤ C*(b+1)+1 := by
        simpa only [Nat.size_pow] using Nat.size_le_size hh.1.2
      have h2 : (parameters d n ν lam).ρ.den.size ≤ C*(b+1)+1 := by
        simpa only [Nat.size_pow] using Nat.size_le_size hh.2.2
      exact (size_mul_le _ _).trans (by omega)
    _ = (N+1)*(2*(C*(b+1)+1)) := by simp

theorem normalized_mesh_polynomial : ∃ C : ℕ, 0<C ∧
    ∀ (d N : ℕ) (coords : Fin N → Fin d × Fin d → ℚ),
      (meshDenominator d N (varianceQuery coords) (penaltyParameter N (varianceQuery coords))).size ≤
        (meshBitsP C).eval (d+N) := by
  obtain ⟨C,hC,hs⟩ := schedule_parts_linear
  refine ⟨C,hC,?_⟩
  intro d N coords
  have hh := mesh_bits_bound (d:=d) (N:=N) C (baseBits d N)
    (varianceQuery coords) (penaltyParameter N (varianceQuery coords)) (fun n hn => by
      have hb := base_parts coords n hn
      exact hs d n _ _ _ hb.1 hb.2.1 hb.2.2.1 hb.2.2.2)
  apply hh.trans
  change 1+(N+1)*(2*(C*(baseBits d N+1)+1)) ≤
    1+(d+N+1)*(2*(C*(baseBitsP.eval (d+N)+1)+1))
  have hb := baseBits_le (d+N) (Nat.le_add_right d N) (Nat.le_add_left N d)
  gcongr
  omega

lemma run_grid (coords : Fin N → Fin d × Fin d → ℚ) (ν lam : ℚ) (k : ℕ) :
    ∀ i, Grid (meshDenominator d N ν lam)
      (run (transition coords ν lam) k (freezeAll (lam^2/ν) 0) i) := by
  apply run_invariant (transition coords ν lam)
    (fun x => ∀ i,Grid (meshDenominator d N ν lam) (x i))
    (fun x y hx hs => transition_grid coords ν lam x y hx hs)
  exact freezeList_grid _ _ (fun _ => Grid.zero _) _

noncomputable section
open CurrentKS.Hermitian CurrentKS.State
open scoped MatrixOrder Matrix.Norms.Frobenius

lemma run_cube [NeZero d] (coords : Fin N → Fin d × Fin d → ℚ)
    (hA : ∀ i,rationalAtoms coords i∈psdCone d)
    (hA0 : ∀ i,rationalAtoms coords i≠0)
    (hrank : ∀ i,(rationalAtoms coords i : Mat d).rank ≤ 1)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
    {ν lam : ℚ} (hν : 0<ν) (hν1 : ν≤1) (hlam : 0<lam) (hlam1 : lam≤1)
    (hvar : varianceH (rationalAtoms coords) ≤ (ν:ℝ) • (Hermitian.one : H d)) (k : ℕ) :
    ∀ i, |run (transition coords ν lam) k (freezeAll (lam^2/ν) 0) i| ≤ 1 := by
  have hP := run_invariant (transition coords ν lam) (StripCube (lam^2/ν))
    (fun x y hx hs => (transition_spec coords hA hA0 hrank htr hν hν1 hlam hlam1 hvar x y hx hs).1)
    k (freezeAll (lam^2/ν) 0) (freezeAll_stripCube (lam^2/ν) 0 (by simp))
  exact hP.1

theorem normalized_stored_bits_polynomial : ∃ p : NaturalPolynomial,
    ∀ (d N : ℕ) [NeZero d] [NeZero N] (coords : Fin N → Fin d × Fin d → ℚ),
    (∀ i,rationalAtoms coords i∈psdCone d) → (∀ i,rationalAtoms coords i≠0) →
    (∀ i,(rationalAtoms coords i : Mat d).rank ≤ 1) →
    (∑ i,Hermitian.realTrace (rationalAtoms coords i)=1) →
    ∀ k i, let ν := varianceQuery coords; let lam := penaltyParameter N ν
      bitSize (run (transition coords ν lam) k (freezeAll (lam^2/ν) 0) i) ≤ p.eval (d+N) := by
  obtain ⟨C,_,hC⟩ := normalized_mesh_polynomial
  refine ⟨storedBitsP C,?_⟩
  intro d N _ _ coords hA hA0 hrank htr k i
  let ν := varianceQuery coords
  let lam := penaltyParameter N ν
  have hν := varianceQuery_spec coords hA hrank htr
  have hl := penaltyParameter_pos_le (NeZero.pos N) hν.1 hν.2.1
  have hvar : varianceH (rationalAtoms coords) ≤ (ν:ℝ) • (Hermitian.one : H d) :=
    (le_operatorNorm_smul_one _).trans (scalar_one_mono hν.2.2.1)
  have hc := run_cube coords hA hA0 hrank htr hν.1 hν.2.1 hl.1 hl.2 hvar k i
  have hb := coordinate_bit_bound (meshDenominator_pos d N ν lam) (run_grid coords ν lam k i) hc
  exact hb.trans (Nat.mul_le_mul_left 2 (hC d N coords))
end
end CurrentKS.RationalFace

end OAI
