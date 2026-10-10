import OAI.Combinatorics.HoneycombChords.Geometry

namespace OAI

/-!
# Critical honeycomb tile weights

Formalized from *Critical honeycomb chords with prescribed boundary endpoints*
(OpenAI, September 26, 2026).
-/

namespace CriticalHoneycombTransfer
noncomputable def L : ℝ := Real.pi / 8
noncomputable def S : ℝ := Real.sin (2 * L)
noncomputable def b : ℝ := 3 * L
noncomputable def Q (u : ℝ) : ℝ := Real.sin (2*L+u) * Real.sin (b+u)
noncomputable def a (u : ℝ) : ℝ := S * Real.sin (b-u) / Q u
noncomputable def h (u : ℝ) : ℝ := S * Real.sin u / Q u
noncomputable def v (u : ℝ) : ℝ := Real.sin (b-u) * Real.sin u / Q u
noncomputable def c (u : ℝ) : ℝ := Real.sin (b-u) * Real.sin (2*L-u) / Q u
noncomputable def d (u : ℝ) : ℝ := Real.sin u * Real.sin (u-L) / Q u
noncomputable def κ : ℝ := (2 + Real.sqrt 2) ^ (-(1:ℝ)/2)

 theorem κ_eq_inv_sqrt : κ = (Real.sqrt (2 + Real.sqrt 2))⁻¹ := by
  rw [κ, neg_div, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]

 theorem L_pos : 0 < L := by unfold L; positivity
 theorem L_lt_pi_div_two : L < Real.pi / 2 := by unfold L; linarith [Real.pi_pos]
 theorem cos_L_pos : 0 < Real.cos L := by
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith [L_pos, Real.pi_pos], L_lt_pi_div_two⟩
 theorem sin_two_L : Real.sin (2*L) = Real.sqrt 2 / 2 := by
  convert Real.sin_pi_div_four using 1
  congr 1
  unfold L
  ring
 theorem cos_two_L : Real.cos (2*L) = Real.sqrt 2 / 2 := by
  convert Real.cos_pi_div_four using 1
  congr 1
  unfold L
  ring
 theorem sin_three_L : Real.sin (3*L) = Real.cos L := by
  have hh : 3*L = Real.pi/2 - L := by unfold L; ring
  rw [hh, Real.sin_pi_div_two_sub]
 theorem sin_four_L : Real.sin (4*L) = 1 := by
  have hh : 4*L = Real.pi/2 := by unfold L; ring
  rw [hh, Real.sin_pi_div_two]
 theorem four_cos_sq : (2 * Real.cos L)^2 = 2 + Real.sqrt 2 := by
  have hh := Real.cos_two_mul L
  rw [cos_two_L] at hh
  nlinarith
 theorem κ_cos : 2 * κ * Real.cos L = 1 := by
  have hh : Real.sqrt (2 + Real.sqrt 2) = 2 * Real.cos L := by
    rw [← four_cos_sq, Real.sqrt_sq (mul_nonneg (by norm_num) (le_of_lt cos_L_pos))]
  rw [κ_eq_inv_sqrt, hh]
  field_simp [ne_of_gt cos_L_pos]

 theorem physical_weights :
     a L = κ ∧ h L = κ^2 ∧ v L = κ^2 ∧ c L = κ^2 ∧ d L = 0 := by
  have hQ : Q L = Real.cos L := by
    unfold Q b
    convert congrArg (fun x : ℝ => x * 1) sin_three_L using 1 <;>
      simp only [mul_one]
    rw [show 2*L + L = 3*L by ring, show 3*L+L=4*L by ring,
      sin_four_L, mul_one]
  have hS : S = Real.sqrt 2 / 2 := sin_two_L
  have hsq : (Real.sqrt 2)^2 = 2 := by norm_num
  have ha : a L = κ := by
    unfold a b
    rw [hQ, show 3*L-L=2*L by ring, sin_two_L, hS]
    apply (div_eq_iff (ne_of_gt cos_L_pos)).mpr
    nlinarith only [κ_cos, hsq]
  have hh : h L = κ^2 := by
    unfold h
    rw [hQ, hS]
    apply (div_eq_iff (ne_of_gt cos_L_pos)).mpr
    have ht := Real.sin_two_mul L
    rw [sin_two_L] at ht
    have hmul := congrArg (fun x : ℝ => x * (Real.sqrt 2)) ht
    have he : (Real.sqrt 2 / 2 * Real.sin L) * Real.cos L = 1/4 := by
      nlinarith only [hmul, hsq]
    have he' : (κ / 2) * Real.cos L = 1/4 := by
      nlinarith only [κ_cos, hsq]
    have hsin : Real.sqrt 2 / 2 * Real.sin L = κ/2 :=
      (mul_right_cancel₀ (ne_of_gt cos_L_pos)) (he.trans he'.symm)
    have hk := congrArg (fun x : ℝ => x * κ) κ_cos
    rw [hsin]
    nlinarith only [hk]
  refine ⟨ha,hh,?_,?_,?_⟩
  · convert hh using 1
    unfold v h b S
    rw [show 3*L-L=2*L by ring]
  · convert hh using 1
    unfold c h b S
    rw [show 3*L-L=2*L by ring, show 2*L-L=L by ring]
  · simp [d]
end CriticalHoneycombTransfer


namespace CriticalHoneycomb.Transfer.Planar
open scoped BigOperators

noncomputable def angle : ℝ := Real.pi / 8
noncomputable def bigAngle : ℝ := 3 * angle
noncomputable def sine2 : ℝ := Real.sin (2 * angle)
noncomputable def denominator (u : ℝ) : ℝ :=
  Real.sin (2 * angle + u) * Real.sin (bigAngle + u)

noncomputable def a (u : ℝ) : ℝ :=
  sine2 * Real.sin (bigAngle - u) / denominator u
noncomputable def h (u : ℝ) : ℝ :=
  sine2 * Real.sin u / denominator u
noncomputable def v (u : ℝ) : ℝ :=
  Real.sin (bigAngle - u) * Real.sin u / denominator u
noncomputable def c (u : ℝ) : ℝ :=
  Real.sin (bigAngle - u) * Real.sin (2 * angle - u) / denominator u
noncomputable def d (u : ℝ) : ℝ :=
  Real.sin u * Real.sin (u - angle) / denominator u

noncomputable def phase : ℂ := Complex.exp ((2 * angle : ℝ) * Complex.I)

lemma phase_sq : phase^2 = Complex.I := by
  unfold phase
  rw [← Complex.exp_nat_mul]
  convert Complex.exp_pi_div_two_mul_I using 1
  push_cast
  unfold angle
  push_cast
  ring_nf

lemma phase_ne_zero : phase ≠ 0 := Complex.exp_ne_zero _

lemma phase_inv : phase⁻¹ = -phase * Complex.I := by
  apply mul_left_cancel₀ phase_ne_zero
  rw [mul_inv_cancel₀ phase_ne_zero]
  calc
    1 = -phase^2 * Complex.I := by rw [phase_sq]; simp
    _ = phase * (-phase * Complex.I) := by ring

/-!
Planar local-to-global identity for the physical crossing observable.
The full source R is displayed with its diagonal spin order +,0,-.
`braidR` is the planar tile after exchanging its two output slots.
-/
noncomputable def sourceR (a h v c d : ℂ) (p q : Fin 3 × Fin 3) : ℂ :=
  match p.1.val, p.2.val, q.1.val, q.2.val with
  | 0, 0, 0, 0 => c
  | 2, 2, 2, 2 => c
  | 0, 1, 0, 1 | 1, 0, 1, 0 | 2, 1, 2, 1 | 1, 2, 1, 2 => v
  | 0, 1, 1, 0 | 1, 0, 0, 1 | 2, 1, 1, 2 | 1, 2, 2, 1 => a
  | 0, 2, 0, 2 => d
  | 0, 2, 1, 1 => h / phase
  | 0, 2, 2, 0 => c+d/phase^2
  | 1, 1, 0, 2 => h*phase
  | 1, 1, 1, 1 => 1
  | 1, 1, 2, 0 => h/phase
  | 2, 0, 0, 2 => c+d*phase^2
  | 2, 0, 1, 1 => h*phase
  | 2, 0, 2, 0 => d
  | _, _, _, _ => 0

noncomputable def cup (i j : Fin 3) : ℂ :=
  if i=0 ∧ j=2 then phase else if i=2 ∧ j=0 then phase⁻¹ else 0

noncomputable def occupied (i j : Fin 3) : ℂ := if i=j ∧ i≠1 then 1 else 0
noncomputable def vacant (i j : Fin 3) : ℂ := if i=1 ∧ j=1 then 1 else 0
noncomputable def empty (i : Fin 3) : ℂ := if i=1 then 1 else 0

/-- Ordinary transpose, not Hermitian adjoint: a closed unoriented loop
has exactly weight zero at the source's phase. -/
theorem loop_erasure : (∑ i : Fin 3, ∑ j : Fin 3, cup i j * cup i j) = 0 := by
  simp [cup, Fin.sum_univ_three]
  rw [← sq, ← sq, inv_pow, phase_sq, Complex.inv_I]
  simp

/-- Straightening a cup-cap pair leaves the occupied strand unchanged. -/
theorem snake_left (i j : Fin 3) :
    (∑ k : Fin 3, cup i k * cup k j) = occupied i j := by
  fin_cases i <;> fin_cases j <;>
    simp [cup, occupied, phase_ne_zero]

theorem snake_right (i j : Fin 3) :
    (∑ k : Fin 3, cup k i * cup j k) = occupied i j := by
  rw [show (∑ k : Fin 3, cup k i * cup j k) = ∑ k : Fin 3, cup j k * cup k i by
    apply Finset.sum_congr rfl; intro k hk; ring]
  rw [snake_left]
  simp only [occupied]
  split_ifs <;> simp_all

/-- Exact dilute Temperley--Lieb decomposition of the source local tile.
The eight connectivities carry precisely the coefficients listed in the
physical crossing observable paragraph. -/
theorem tile_decomposition (a h v c d : ℂ) (i j k l : Fin 3) :
    sourceR a h v c d (j,i) (k,l) =
      vacant i k * vacant j l +
      a * (occupied i k * vacant j l + vacant i k * occupied j l) +
      c * occupied i k * occupied j l +
      v * (empty i * empty l * occupied j k + empty j * empty k * occupied i l) +
      h * (cup i j * empty k * empty l + empty i * empty j * cup k l) +
      d * cup i j * cup k l := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [sourceR, vacant, occupied, empty, cup, phase_ne_zero, div_eq_mul_inv] <;>
    ring

end CriticalHoneycomb.Transfer.Planar

namespace CriticalHoneycomb.Transfer.PhysicalTiles
open scoped BigOperators
open Planar

/-- The eight choices of non-intersecting arcs in one actual triangular pair.
W,S meet the up triangle; E,N meet the down triangle. The forbidden second
two-arc choice would use both centers twice and is absent. -/
inductive Shape
  | empty | westSouth | northEast | both | westNorth | southEast | westEast | northSouth
  deriving DecidableEq
instance : Fintype Shape := ⟨{.empty,.westSouth,.northEast,.both,.westNorth,.southEast,.westEast,.northSouth},
  by intro q; cases q <;> simp⟩

structure Selection where
  west : Bool
  south : Bool
  east : Bool
  north : Bool
  middle : Bool
  deriving DecidableEq, Fintype

def Shape.selection : Shape → Selection
  | .empty => ⟨false,false,false,false,false⟩
  | .westSouth => ⟨true,true,false,false,false⟩
  | .northEast => ⟨false,false,true,true,false⟩
  | .both => ⟨true,true,true,true,false⟩
  | .westNorth => ⟨true,false,false,true,true⟩
  | .southEast => ⟨false,true,true,false,true⟩
  | .westEast => ⟨true,false,true,false,true⟩
  | .northSouth => ⟨false,true,false,true,true⟩

def Selection.upDegree (s : Selection) : ℕ := s.west.toNat+s.south.toNat+s.middle.toNat
def Selection.downDegree (s : Selection) : ℕ := s.east.toNat+s.north.toNat+s.middle.toNat

def Admissible (s : Selection) : Prop :=
  (s.upDegree=0 ∨ s.upDegree=2) ∧ (s.downDegree=0 ∨ s.downDegree=2)
instance (s : Selection) : Decidable (Admissible s) := inferInstanceAs (Decidable (_ ∧ _))

/-- Local self-avoiding connectivity classification by both center degrees. -/
theorem selection_classification (s : Selection) :
    Admissible s ↔ ∃ q : Shape, q.selection=s := by
  revert s
  decide

theorem selection_injective : Function.Injective Shape.selection := by decide

def Shape.visits : Shape → ℕ
  | .empty => 0
  | .westSouth | .northEast => 1
  | _ => 2

/-- The actual number of used centers, not the number of ports or arcs. -/
theorem visits_eq (q : Shape) :
    q.visits = (if q.selection.upDegree=0 then 0 else 1) +
      (if q.selection.downDegree=0 then 0 else 1) := by
  cases q <;> rfl

/-- Pure orientation kernel for a local connectivity. Indices are W,N,S,E,
respectively: output order W,N, input order S,E in the braided drawing. -/
noncomputable def shapeTensor (q : Shape) (w n s e : Fin 3) : ℂ :=
  match q with
  | .empty => vacant w s * vacant n e
  | .westSouth => occupied w s * vacant n e
  | .northEast => vacant w s * occupied n e
  | .both => occupied w s * occupied n e
  | .westNorth => cup w n * Planar.empty s * Planar.empty e
  | .southEast => Planar.empty w * Planar.empty n * cup s e
  | .westEast => Planar.empty n * Planar.empty s * occupied w e
  | .northSouth => Planar.empty w * Planar.empty e * occupied n s

/-- Critical weights count precisely the visited centers of the lozenge.
This is a local equality of the exact R entries and actual path choices. -/
theorem physical_tile_expansion (w n s e : Fin 3) :
    sourceR (kappa:ℂ) (kappa^2:ℂ) (kappa^2:ℂ) (kappa^2:ℂ) 0 (n,w) (s,e) =
      ∑ q : Shape, (kappa:ℂ)^q.visits * shapeTensor q w n s e := by
  rw [tile_decomposition]
  change _ = ∑ q ∈ ({.empty,.westSouth,.northEast,.both,.westNorth,.southEast,.westEast,.northSouth} : Finset Shape),
    (kappa:ℂ)^q.visits * shapeTensor q w n s e
  simp [Shape.visits,shapeTensor]
  ring

inductive Node | up | down | west | south | east | north
  deriving DecidableEq
instance : Fintype Node := ⟨{.up,.down,.west,.south,.east,.north},
  by intro q; cases q <;> simp⟩

def Node.position (i j : ℤ) : Node → Center
  | .up => CriticalHoneycomb.up i j
  | .down => CriticalHoneycomb.down i j
  | .west => CriticalHoneycomb.down (i-1) j
  | .south => CriticalHoneycomb.down i (j-1)
  | .east => CriticalHoneycomb.up (i+1) j
  | .north => CriticalHoneycomb.up i (j+1)

def Selection.adj (s : Selection) : Node → Node → Prop
  | .up,.down | .down,.up => s.middle=true
  | .up,.west | .west,.up => s.west=true
  | .up,.south | .south,.up => s.south=true
  | .down,.east | .east,.down => s.east=true
  | .down,.north | .north,.down => s.north=true
  | _,_ => False
instance (s : Selection) (a b : Node) : Decidable (s.adj a b) := by
  cases a <;> cases b <;> unfold Selection.adj <;> infer_instance

/-- Every selected local edge is the exact source honeycomb adjacency. -/
theorem selected_adjacent (s : Selection) (i j : ℤ) (a b : Node)
    (h : s.adj a b) : Adj (a.position i j) (b.position i j) := by
  cases a <;> cases b <;>
    simp_all [Selection.adj,Node.position,Adj,CriticalHoneycomb.up,CriticalHoneycomb.down] 

/-- The local graph contains genuinely distinct centers, including its
four exterior neighbor centers; no loop or collision is hidden by the drawing. -/
theorem node_position_injective (i j : ℤ) : Function.Injective (Node.position i j) := by
  intro a b h
  cases a <;> cases b <;>
    simp_all [Node.position,CriticalHoneycomb.up,CriticalHoneycomb.down] <;> omega

end CriticalHoneycomb.Transfer.PhysicalTiles

namespace CriticalHoneycomb.Transfer.PhysicalTiles
open scoped BigOperators
open Planar

/-- The actual spectral weights, at the physical honeycomb specialization,
are the exact local path expansion above. No R entries are altered. -/
theorem spectral_physical_tile_expansion (w n s e : Fin 3) :
    sourceR (CriticalHoneycombTransfer.a CriticalHoneycombTransfer.L : ℂ)
      (CriticalHoneycombTransfer.h CriticalHoneycombTransfer.L : ℂ)
      (CriticalHoneycombTransfer.v CriticalHoneycombTransfer.L : ℂ)
      (CriticalHoneycombTransfer.c CriticalHoneycombTransfer.L : ℂ)
      (CriticalHoneycombTransfer.d CriticalHoneycombTransfer.L : ℂ) (n,w) (s,e) =
      ∑ q : Shape, (kappa:ℂ)^q.visits * shapeTensor q w n s e := by
  obtain ⟨ha,hh,hv,hc,hd⟩ := CriticalHoneycombTransfer.physical_weights
  rw [ha,hh,hv,hc,hd]
  simpa only [Complex.ofReal_pow,Complex.ofReal_zero,CriticalHoneycombTransfer.κ,kappa] using physical_tile_expansion w n s e

end CriticalHoneycomb.Transfer.PhysicalTiles

end OAI
