import OAI.Combinatorics.HoneycombChords.ChordRemoval

namespace OAI

/-!
# Finite honeycomb current conservation

Formalized from *Critical honeycomb chords with prescribed boundary endpoints*
(OpenAI, September 26, 2026).
-/

namespace CriticalHoneycomb.Transfer.FluxWard
open PhysicalTiles Planar
open scoped BigOperators

noncomputable def r : ℂ := Complex.exp (((Real.pi/8:ℝ):ℂ)*Complex.I)
lemma r_ne_zero : r≠0 := Complex.exp_ne_zero _
lemma r_sq : r^2=phase := by
  unfold r phase angle
  rw [←Complex.exp_nat_mul]
  congr 1
  push_cast
  ring
lemma r_eight : r^8 = -1 := by
  rw [show (8:ℕ)=2*4 by omega,pow_mul,r_sq,show (4:ℕ)=2*2 by omega,pow_mul,phase_sq]
  simp
lemma r_inverse : r⁻¹= -r^7 := by
  apply mul_left_cancel₀ r_ne_zero
  rw [mul_inv_cancel₀ r_ne_zero]
  have h : r * (-r^7) = -(r^8) := by ring
  rw [h,r_eight]
  simp
lemma phase_q : phase=r^2 := r_sq.symm
lemma phase_inv_q : phase⁻¹= -r^6 := by
  rw [phase_q,←inv_pow,r_inverse]
  have h : r^14=r^6*r^8 := by ring
  rw [show (-r^7)^2=r^14 by ring,h,r_eight]
  ring
lemma kappa_phase : (kappa:ℂ)*(r+r⁻¹)=1 := by
  have hr : r+r⁻¹=(2*Real.cos (Real.pi/8):ℝ) := by
    rw [r,←Complex.exp_neg]
    have hn : -(((Real.pi/8:ℝ):ℂ)*Complex.I)=((- (Real.pi/8):ℝ):ℂ)*Complex.I := by push_cast; ring
    rw [hn,Complex.exp_ofReal_mul_I,Complex.exp_ofReal_mul_I]
    simp only [Real.cos_neg,Real.sin_neg]
    push_cast
    ring
  rw [hr]
  have h := Complex.ofReal_inj.mpr CriticalHoneycombTransfer.κ_cos
  convert h using 1 ; simp [kappa,CriticalHoneycombTransfer.κ,CriticalHoneycombTransfer.L] ; ring

/-- Off-diagonal raising generator, in the source order +, vacant, -. -/
def raising (i j : Fin 3) : ℂ :=
  if i=0 ∧ j=1 then 1 else if i=1 ∧ j=2 then -1 else 0
/-- Diagonal quantum-group weight, with q=exp(5πi/8). -/
noncomputable def twist (i : Fin 3) : ℂ :=
  if i=0 then r^5 else if i=1 then 1 else -r^3
noncomputable def untwist (i : Fin 3) : ℂ :=
  if i=0 then -r^3 else if i=1 then 1 else r^5

lemma twist_inverse (i : Fin 3) : twist i * untwist i=1 := by
  fin_cases i <;> norm_num [twist,untwist]
  all_goals calc
    _ = -(r^8) := by ring
    _ = 1 := by rw [r_eight]; ring

lemma weight_equation : (kappa:ℂ)*(r^2+1)=r := by
  have h := congrArg (fun z : ℂ=>z*r) kappa_phase
  simpa [mul_add,add_mul,mul_assoc,r_ne_zero,pow_two] using h

lemma kappa_polynomial : (kappa:ℂ)=(r-r^3+r^5-r^7)/2 := by
  linear_combination (1-r^2+r^4-r^6)/2 * weight_equation + (kappa:ℂ)/2 * r_eight

lemma r_power_reduce (n : ℕ) : r^n=(-1:ℂ)^(n/8)*r^(n%8) := by
  calc
    r^n = r^(n%8+8*(n/8)) := congrArg (r^·) (Nat.mod_add_div n 8).symm
    _ = _ := by rw [pow_add,pow_mul,r_eight]; ring

lemma r_pow_8 : r^8 = -(1:ℂ) := by
  have h := r_power_reduce 8
  norm_num at h ⊢
  exact h
lemma r_pow_9 : r^9 = -r^1 := by
  have h := r_power_reduce 9
  norm_num at h ⊢
  exact h
lemma r_pow_10 : r^10 = -r^2 := by
  have h := r_power_reduce 10
  norm_num at h ⊢
  exact h
lemma r_pow_11 : r^11 = -r^3 := by
  have h := r_power_reduce 11
  norm_num at h ⊢
  exact h
lemma r_pow_12 : r^12 = -r^4 := by
  have h := r_power_reduce 12
  norm_num at h ⊢
  exact h
lemma r_pow_13 : r^13 = -r^5 := by
  have h := r_power_reduce 13
  norm_num at h ⊢
  exact h
lemma r_pow_14 : r^14 = -r^6 := by
  have h := r_power_reduce 14
  norm_num at h ⊢
  exact h
lemma r_pow_15 : r^15 = -r^7 := by
  have h := r_power_reduce 15
  norm_num at h ⊢
  exact h
lemma r_pow_16 : r^16 = (1:ℂ) := by
  have h := r_power_reduce 16
  norm_num at h ⊢
  exact h
lemma r_pow_17 : r^17 = r^1 := by
  have h := r_power_reduce 17
  norm_num at h ⊢
  exact h
lemma r_pow_18 : r^18 = r^2 := by
  have h := r_power_reduce 18
  norm_num at h ⊢
  exact h
lemma r_pow_19 : r^19 = r^3 := by
  have h := r_power_reduce 19
  norm_num at h ⊢
  exact h
lemma r_pow_20 : r^20 = r^4 := by
  have h := r_power_reduce 20
  norm_num at h ⊢
  exact h
lemma r_pow_21 : r^21 = r^5 := by
  have h := r_power_reduce 21
  norm_num at h ⊢
  exact h
lemma r_pow_22 : r^22 = r^6 := by
  have h := r_power_reduce 22
  norm_num at h ⊢
  exact h
lemma r_pow_23 : r^23 = r^7 := by
  have h := r_power_reduce 23
  norm_num at h ⊢
  exact h
lemma r_pow_24 : r^24 = -(1:ℂ) := by
  have h := r_power_reduce 24
  norm_num at h ⊢
  exact h
lemma r_pow_25 : r^25 = -r^1 := by
  have h := r_power_reduce 25
  norm_num at h ⊢
  exact h
lemma r_pow_26 : r^26 = -r^2 := by
  have h := r_power_reduce 26
  norm_num at h ⊢
  exact h
lemma r_pow_27 : r^27 = -r^3 := by
  have h := r_power_reduce 27
  norm_num at h ⊢
  exact h
lemma r_pow_28 : r^28 = -r^4 := by
  have h := r_power_reduce 28
  norm_num at h ⊢
  exact h
lemma r_pow_29 : r^29 = -r^5 := by
  have h := r_power_reduce 29
  norm_num at h ⊢
  exact h
lemma r_pow_30 : r^30 = -r^6 := by
  have h := r_power_reduce 30
  norm_num at h ⊢
  exact h
lemma r_pow_31 : r^31 = -r^7 := by
  have h := r_power_reduce 31
  norm_num at h ⊢
  exact h
lemma r_pow_32 : r^32 = (1:ℂ) := by
  have h := r_power_reduce 32
  norm_num at h ⊢
  exact h

lemma inverse_r_sq : (r^2)⁻¹= -r^6 := by rw [←phase_q]; exact phase_inv_q

/-- Local current conservation at a single actual up-triangle center. -/
theorem up_current (w a b : Fin 3) :
    (∑ v : Fin 3, raising w v * upTensor v a b) =
      r * (∑ v : Fin 3, upTensor w v b * raising v a * twist b) +
      r⁻¹ * (∑ v : Fin 3, upTensor w a v * untwist a * raising v b) := by
  fin_cases w <;> fin_cases a <;> fin_cases b <;>
    simp [raising,twist,untwist,upTensor,occupied,Planar.empty,cup,Fin.sum_univ_three,
      phase_q,inverse_r_sq,r_inverse] <;>
    rw [kappa_polynomial] <;> ring_nf <;>
    simp only [r_pow_8,r_pow_9,r_pow_10,r_pow_11,r_pow_12,r_pow_13,r_pow_14,r_pow_15,r_pow_17,r_pow_19,r_pow_21,r_pow_23,r_pow_25,] <;> ring

noncomputable def physicalTile (w n s e : Fin 3) : ℂ :=
  sourceR (kappa:ℂ) (kappa^2:ℂ) (kappa^2:ℂ) (kappa^2:ℂ) 0 (n,w) (s,e)

theorem tile_twist (w n s e : Fin 3) :
    twist w * twist n * physicalTile w n s e = physicalTile w n s e * twist s * twist e := by
  fin_cases w <;> fin_cases n <;> fin_cases s <;> fin_cases e <;>
    simp [twist,physicalTile,sourceR] <;> ring_nf <;> simp only [r_eight] <;> ring

theorem tile_untwist (w n s e : Fin 3) :
    untwist w * untwist n * physicalTile w n s e = physicalTile w n s e * untwist s * untwist e := by
  fin_cases w <;> fin_cases n <;> fin_cases s <;> fin_cases e <;>
    simp [untwist,physicalTile,sourceR] <;> ring_nf <;> simp only [r_eight] <;> ring

private theorem tile_current_00 (s e : Fin 3) :
    (∑ v : Fin 3, raising 0 v * twist 0 * physicalTile v 0 s e) +
      r * (∑ v : Fin 3, untwist 0 * raising 0 v * physicalTile 0 v s e) =
      r * (∑ v : Fin 3, physicalTile 0 0 v e * raising v s * twist e) +
      (∑ v : Fin 3, physicalTile 0 0 s v * untwist s * raising v e) := by
  fin_cases s <;> fin_cases e <;>
    simp [raising,twist,untwist,physicalTile,sourceR,phase_q,inverse_r_sq,div_eq_mul_inv] <;>
    simp only [kappa_polynomial] <;> ring_nf <;>
    simp only [r_pow_8,r_pow_9,r_pow_10,r_pow_11,r_pow_12,r_pow_13,r_pow_14,r_pow_15,r_pow_16,r_pow_17,r_pow_18,r_pow_19,r_pow_20,] <;> ring

private theorem tile_current_01 (s e : Fin 3) :
    (∑ v : Fin 3, raising 0 v * twist 1 * physicalTile v 1 s e) +
      r * (∑ v : Fin 3, untwist 0 * raising 1 v * physicalTile 0 v s e) =
      r * (∑ v : Fin 3, physicalTile 0 1 v e * raising v s * twist e) +
      (∑ v : Fin 3, physicalTile 0 1 s v * untwist s * raising v e) := by
  fin_cases s <;> fin_cases e <;>
    simp [raising,twist,untwist,physicalTile,sourceR,phase_q,inverse_r_sq,div_eq_mul_inv] <;>
    simp only [kappa_polynomial] <;> ring_nf <;>
    simp only [r_pow_8,r_pow_10,r_pow_12,r_pow_14,r_pow_16,r_pow_18,r_pow_20,] <;> ring

private theorem tile_current_02 (s e : Fin 3) :
    (∑ v : Fin 3, raising 0 v * twist 2 * physicalTile v 2 s e) +
      r * (∑ v : Fin 3, untwist 0 * raising 2 v * physicalTile 0 v s e) =
      r * (∑ v : Fin 3, physicalTile 0 2 v e * raising v s * twist e) +
      (∑ v : Fin 3, physicalTile 0 2 s v * untwist s * raising v e) := by
  fin_cases s <;> fin_cases e <;>
    simp [raising,twist,untwist,physicalTile,sourceR,phase_q,inverse_r_sq,div_eq_mul_inv] <;>
    simp only [kappa_polynomial] <;> ring_nf ;
    simp only [r_pow_8,r_pow_10,r_pow_12,r_pow_14,r_pow_16,r_pow_18,] ; ring

private theorem tile_current_10 (s e : Fin 3) :
    (∑ v : Fin 3, raising 1 v * twist 0 * physicalTile v 0 s e) +
      r * (∑ v : Fin 3, untwist 1 * raising 0 v * physicalTile 1 v s e) =
      r * (∑ v : Fin 3, physicalTile 1 0 v e * raising v s * twist e) +
      (∑ v : Fin 3, physicalTile 1 0 s v * untwist s * raising v e) := by
  fin_cases s <;> fin_cases e <;>
    simp [raising,twist,untwist,physicalTile,sourceR,phase_q,inverse_r_sq,div_eq_mul_inv] <;>
    simp only [kappa_polynomial] <;> ring_nf <;>
    simp only [r_pow_9,r_pow_11,r_pow_13,r_pow_15,r_pow_17,r_pow_19,r_pow_21,r_pow_23,r_pow_25,] <;> ring

private theorem tile_current_11 (s e : Fin 3) :
    (∑ v : Fin 3, raising 1 v * twist 1 * physicalTile v 1 s e) +
      r * (∑ v : Fin 3, untwist 1 * raising 1 v * physicalTile 1 v s e) =
      r * (∑ v : Fin 3, physicalTile 1 1 v e * raising v s * twist e) +
      (∑ v : Fin 3, physicalTile 1 1 s v * untwist s * raising v e) := by
  fin_cases s <;> fin_cases e <;>
    simp [raising,twist,untwist,physicalTile,sourceR,phase_q,inverse_r_sq,div_eq_mul_inv] <;>
    simp only [kappa_polynomial] <;> ring_nf <;>
    simp only [r_pow_8,r_pow_9,r_pow_10,r_pow_11,r_pow_12,r_pow_13,r_pow_14,r_pow_15,r_pow_16,r_pow_17,r_pow_18,r_pow_19,r_pow_20,r_pow_21,r_pow_23,r_pow_25,] <;> ring

private theorem tile_current_12 (s e : Fin 3) :
    (∑ v : Fin 3, raising 1 v * twist 2 * physicalTile v 2 s e) +
      r * (∑ v : Fin 3, untwist 1 * raising 2 v * physicalTile 1 v s e) =
      r * (∑ v : Fin 3, physicalTile 1 2 v e * raising v s * twist e) +
      (∑ v : Fin 3, physicalTile 1 2 s v * untwist s * raising v e) := by
  fin_cases s <;> fin_cases e <;>
    simp [raising,twist,untwist,physicalTile,sourceR,phase_q,inverse_r_sq,div_eq_mul_inv] ;
    simp only [kappa_polynomial] ; ring_nf ;
    simp only [r_pow_9,r_pow_11,r_pow_13,r_pow_15,r_pow_17,r_pow_19,] ; ring

private theorem tile_current_20 (s e : Fin 3) :
    (∑ v : Fin 3, raising 2 v * twist 0 * physicalTile v 0 s e) +
      r * (∑ v : Fin 3, untwist 2 * raising 0 v * physicalTile 2 v s e) =
      r * (∑ v : Fin 3, physicalTile 2 0 v e * raising v s * twist e) +
      (∑ v : Fin 3, physicalTile 2 0 s v * untwist s * raising v e) := by
  fin_cases s <;> fin_cases e <;>
    simp [raising,twist,untwist,physicalTile,sourceR,phase_q,inverse_r_sq,div_eq_mul_inv] <;>
    simp only [kappa_polynomial] <;> ring_nf ;
    simp only [r_pow_9,r_pow_11,r_pow_13,r_pow_15,r_pow_17,r_pow_19,r_pow_21,] ; ring

private theorem tile_current_21 (s e : Fin 3) :
    (∑ v : Fin 3, raising 2 v * twist 1 * physicalTile v 1 s e) +
      r * (∑ v : Fin 3, untwist 2 * raising 1 v * physicalTile 2 v s e) =
      r * (∑ v : Fin 3, physicalTile 2 1 v e * raising v s * twist e) +
      (∑ v : Fin 3, physicalTile 2 1 s v * untwist s * raising v e) := by
  fin_cases s <;> fin_cases e <;>
    simp [raising,twist,untwist,physicalTile,sourceR,phase_q,inverse_r_sq,div_eq_mul_inv] ;
    simp only [kappa_polynomial] ; ring_nf ;
    simp only [r_pow_8,r_pow_10,r_pow_12,r_pow_14,r_pow_16,r_pow_18,r_pow_20,] ; ring

private theorem tile_current_22 (s e : Fin 3) :
    (∑ v : Fin 3, raising 2 v * twist 2 * physicalTile v 2 s e) +
      r * (∑ v : Fin 3, untwist 2 * raising 2 v * physicalTile 2 v s e) =
      r * (∑ v : Fin 3, physicalTile 2 2 v e * raising v s * twist e) +
      (∑ v : Fin 3, physicalTile 2 2 s v * untwist s * raising v e) := by
  fin_cases s <;> fin_cases e <;>
    simp [raising,twist,untwist,physicalTile,sourceR,phase_q,inverse_r_sq,div_eq_mul_inv] 

/-- The exact R tile transports the weighted current (r,1) to (1,r).
Its phases and κ are those of the original honeycomb model. -/
theorem tile_current (w n s e : Fin 3) :
    (∑ v : Fin 3, raising w v * twist n * physicalTile v n s e) +
      r * (∑ v : Fin 3, untwist w * raising n v * physicalTile w v s e) =
      r * (∑ v : Fin 3, physicalTile w n v e * raising v s * twist e) +
      (∑ v : Fin 3, physicalTile w n s v * untwist s * raising v e) := by
  fin_cases w <;> fin_cases n
  · exact tile_current_00 s e
  · exact tile_current_01 s e
  · exact tile_current_02 s e
  · exact tile_current_10 s e
  · exact tile_current_11 s e
  · exact tile_current_12 s e
  · exact tile_current_20 s e
  · exact tile_current_21 s e
  · exact tile_current_22 s e

end CriticalHoneycomb.Transfer.FluxWard

namespace CriticalHoneycomb.Transfer.FluxWard
open scoped BigOperators

abbrev FState := List (Fin 3) → ℂ
noncomputable def twistProduct (xs : List (Fin 3)) : ℂ := (xs.map twist).prod
noncomputable def untwistProduct (xs : List (Fin 3)) : ℂ := (xs.map untwist).prod

noncomputable def siteAct : ℕ → FState → FState
  | 0, f, x::y::xs => ∑ a : Fin 3, ∑ b : Fin 3, physicalTile x y a b * f (a::b::xs)
  | 0, _, _ => 0
  | i+1, f, x::xs => siteAct i (fun ys=>f (x::ys)) xs
  | _+1, _, [] => 0

/-- The coproduct of the actual spin-raising current, with direction
weights attached to the boundary wires in their planar contour order. -/
noncomputable def current : List ℂ → FState → FState
  | [], _, _ => 0
  | q::qs, f, x::xs =>
      q * (∑ y : Fin 3, raising x y * f (y::xs)) * twistProduct xs +
      untwist x * current qs (fun ys=>f (x::ys)) xs
  | _::_, _, [] => 0

lemma siteAct_add (i : ℕ) (f g : FState) :
    siteAct i (f+g)=siteAct i f+siteAct i g := by
  induction i generalizing f g with
  | zero =>
    funext xs
    cases xs with
    | nil => simp [siteAct]
    | cons x xs => cases xs <;> simp [siteAct,mul_add,Finset.sum_add_distrib]
  | succ i ih =>
    funext xs
    cases xs with
    | nil => simp [siteAct]
    | cons x xs => exact congrFun (ih (fun ys=>f (x::ys)) (fun ys=>g (x::ys))) xs

lemma siteAct_smul (i : ℕ) (z : ℂ) (f : FState) :
    siteAct i (z • f)=z • siteAct i f := by
  induction i generalizing f with
  | zero =>
    funext xs
    cases xs with
    | nil => simp [siteAct]
    | cons x xs => cases xs <;> simp [siteAct,Finset.mul_sum,mul_left_comm]
  | succ i ih =>
    funext xs
    cases xs with
    | nil => simp [siteAct]
    | cons x xs => exact congrFun (ih (fun ys=>f (x::ys))) xs

noncomputable def siteLinear (i : ℕ) : FState →ₗ[ℂ] FState where
  toFun := siteAct i
  map_add' := siteAct_add i
  map_smul' := siteAct_smul i

lemma current_add (qs : List ℂ) (f g : FState) :
    current qs (f+g)=current qs f+current qs g := by
  induction qs generalizing f g with
  | nil => ext xs; simp [current]
  | cons q qs ih =>
    funext xs
    cases xs with
    | nil => simp [current]
    | cons x xs =>
      simp only [current,Pi.add_apply,mul_add,Finset.sum_add_distrib,add_mul]
      rw [show (fun ys=>f (x::ys)+g (x::ys))=(fun ys=>f (x::ys))+(fun ys=>g (x::ys)) from rfl,
        ih]
      simp only [Pi.add_apply,mul_add]
      ring

lemma current_smul (qs : List ℂ) (z : ℂ) (f : FState) :
    current qs (z • f)=z • current qs f := by
  induction qs generalizing f with
  | nil => ext xs; simp [current]
  | cons q qs ih =>
    funext xs
    cases xs with
    | nil => simp [current]
    | cons x xs =>
      change q * (∑ y, raising x y * (z*f (y::xs))) * twistProduct xs +
        untwist x * current qs (z • (fun ys=>f (x::ys))) xs = _
      rw [ih]
      simp only [Pi.smul_apply,smul_eq_mul]
      simp only [mul_left_comm (raising _ _) z,←Finset.mul_sum]
      simp only [current,]
      ring

noncomputable def currentLinear (qs : List ℂ) : FState →ₗ[ℂ] FState where
  toFun := current qs
  map_add' := current_add qs
  map_smul' := current_smul qs

lemma siteAct_sum {α : Type*} [Fintype α] (i : ℕ) (f : α → FState) (xs) :
    siteAct i (fun ys=>∑ a, f a ys) xs = ∑ a, siteAct i (f a) xs := by
  have h := congrFun (map_sum (siteLinear i) f Finset.univ) xs
  change siteAct i (∑ a, f a) xs = (∑ a, siteAct i (f a)) xs at h
  rw [show (∑ a, f a)=(fun ys=>∑ a, f a ys) from by funext ys; exact Finset.sum_apply ..] at h
  simpa only [Finset.sum_apply] using h

lemma current_sum {α : Type*} [Fintype α] (qs : List ℂ) (f : α → FState) (xs) :
    current qs (fun ys=>∑ a, f a ys) xs = ∑ a, current qs (f a) xs := by
  have h := congrFun (map_sum (currentLinear qs) f Finset.univ) xs
  change current qs (∑ a, f a) xs = (∑ a, current qs (f a)) xs at h
  rw [show (∑ a, f a)=(fun ys=>∑ a, f a ys) from by funext ys; exact Finset.sum_apply ..] at h
  simpa only [Finset.sum_apply] using h

lemma siteAct_scalar (i : ℕ) (z : ℂ) (f : FState) (xs) :
    siteAct i (fun ys=>z*f ys) xs = z*siteAct i f xs :=
  congrFun (siteAct_smul i z f) xs
lemma current_scalar (qs : List ℂ) (z : ℂ) (f : FState) (xs) :
    current qs (fun ys=>z*f ys) xs = z*current qs f xs :=
  congrFun (current_smul qs z f) xs

lemma siteAct_twist (i : ℕ) (f : FState) (xs) :
    siteAct i (fun ys=>twistProduct ys*f ys) xs = twistProduct xs*siteAct i f xs := by
  induction i generalizing f xs with
  | zero =>
    cases xs with
    | nil => simp [siteAct]
    | cons x xs => cases xs with
      | nil => simp [siteAct]
      | cons y xs =>
        simp only [siteAct,twistProduct,List.map_cons,List.prod_cons,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        have h := tile_twist x y a b
        calc
          _ = (physicalTile x y a b * twist a * twist b) * (xs.map twist).prod * f (a::b::xs) := by ring
          _ = _ := by rw [←h]; ring
  | succ i ih =>
    cases xs with
    | nil => simp [siteAct]
    | cons x xs =>
      simp only [siteAct,twistProduct,List.map_cons,List.prod_cons]
      rw [show (fun ys=>(twist x*(ys.map twist).prod)*f (x::ys))=
          (fun ys=>twist x*(twistProduct ys*f (x::ys))) from by funext ys; simp [twistProduct]; ring,
        siteAct_scalar,ih]
      simp [twistProduct,mul_assoc]

open Matrix
open scoped Matrix
abbrev TwoSpin := Fin 3 × Fin 3
noncomputable def pairCurrent (u v : ℂ) : Matrix TwoSpin TwoSpin ℂ := fun o i =>
  (if o.2=i.2 then u*raising o.1 i.1*twist o.2 else 0) +
  (if o.1=i.1 then v*untwist o.1*raising o.2 i.2 else 0)
noncomputable def tileMatrix : Matrix TwoSpin TwoSpin ℂ := fun o i => physicalTile o.1 o.2 i.1 i.2

lemma pairCurrent_left (u v : ℂ) (M : Matrix TwoSpin TwoSpin ℂ) (o i : TwoSpin) :
    (pairCurrent u v * M) o i =
      u*(∑ a, raising o.1 a * twist o.2 * M (a,o.2) i) +
      v*(∑ b, untwist o.1 * raising o.2 b * M (o.1,b) i) := by
  simp only [Matrix.mul_apply,Fintype.sum_prod_type,pairCurrent,add_mul,
    Finset.sum_add_distrib,ite_mul,zero_mul,Finset.mul_sum]
  rw [Finset.sum_comm (f:=fun a b=>if o.1=a then (v*untwist o.1*raising o.2 b)*M (a,b) i else 0)]
  simp [mul_assoc,eq_comm]

lemma pairCurrent_right (u v : ℂ) (M : Matrix TwoSpin TwoSpin ℂ) (o i : TwoSpin) :
    (M * pairCurrent u v) o i =
      u*(∑ a, M o (a,i.2) * raising a i.1 * twist i.2) +
      v*(∑ b, M o (i.1,b) * untwist i.1 * raising b i.2) := by
  simp only [Matrix.mul_apply,Fintype.sum_prod_type,pairCurrent,mul_add,
    Finset.sum_add_distrib,mul_ite,mul_zero,Finset.mul_sum]
  rw [Finset.sum_comm (f:=fun a b=>if a=i.1 then M o (a,b)*(v*untwist a*raising b i.2) else 0)]
  simp [mul_assoc,mul_left_comm,mul_comm]

lemma pairCurrent_tile :
    pairCurrent 1 r * tileMatrix = tileMatrix * pairCurrent r 1 := by
  ext o i
  rw [pairCurrent_left,pairCurrent_right]
  simpa only [one_mul,tileMatrix] using tile_current o.1 o.2 i.1 i.2

lemma pairCurrent_act (u v : ℂ) (f : TwoSpin → ℂ) (x y : Fin 3) :
    (pairCurrent u v *ᵥ f) (x,y) =
      u*(∑ a, raising x a * twist y * f (a,y)) +
      v*(∑ b, untwist x * raising y b * f (x,b)) := by
  have h := pairCurrent_left u v (fun o (_ : TwoSpin)=>f o) (x,y) (x,y)
  exact h

lemma current_two (u v : ℂ) (qs : List ℂ) (f : FState) (x y : Fin 3) (xs) :
    current (u::v::qs) f (x::y::xs) =
      (pairCurrent u v *ᵥ (fun p=>f (p.1::p.2::xs))) (x,y) * twistProduct xs +
      untwist x * untwist y * current qs (fun ys=>f (x::y::ys)) xs := by
  have hs : (∑ a, raising x a*twist y*f (a::y::xs)) =
      twist y*(∑ a, raising x a*f (a::y::xs)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  have ht : (∑ b, untwist x*raising y b*f (x::b::xs)) =
      untwist x*(∑ b, raising y b*f (x::b::xs)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    ring
  rw [pairCurrent_act,hs,ht]
  simp only [current,twistProduct,List.map_cons,List.prod_cons]
  ring

lemma siteAct_zero_pair (f : FState) (x y : Fin 3) (xs) :
    siteAct 0 f (x::y::xs) =
      (tileMatrix *ᵥ (fun p=>f (p.1::p.2::xs))) (x,y) := by
  simp only [siteAct,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,tileMatrix]

lemma current_site_tail (qs : List ℂ) (f : FState) (x y : Fin 3) (xs) :
    untwist x * untwist y * current qs (fun ys=>siteAct 0 f (x::y::ys)) xs =
      ∑ a : Fin 3, ∑ b : Fin 3, physicalTile x y a b *
        (untwist a * untwist b * current qs (fun ys=>f (a::b::ys)) xs) := by
  simp only [siteAct,current_sum,current_scalar,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have h := tile_untwist x y a b
  calc
    _ = (untwist x * untwist y * physicalTile x y a b) *
        current qs (fun ys=>f (a::b::ys)) xs := by ring
    _ = _ := by rw [h]; ring

theorem current_site_zero (qs : List ℂ) (f : FState) :
    current (1::r::qs) (siteAct 0 f) = siteAct 0 (current (r::1::qs) f) := by
  funext xs
  cases xs with
  | nil => simp [current,siteAct]
  | cons x xs => cases xs with
    | nil => simp [current,siteAct]
    | cons y xs =>
      rw [current_two,current_site_tail]
      simp only [siteAct_zero_pair]
      rw [Matrix.mulVec_mulVec,pairCurrent_tile,←Matrix.mulVec_mulVec]
      simp only [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,tileMatrix,
        current_two,Finset.sum_mul]
      simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_mul,mul_assoc]

lemma siteAct_pointwise_add (i : ℕ) (f g : FState) (xs) :
    siteAct i (fun ys=>f ys+g ys) xs = siteAct i f xs+siteAct i g xs :=
  congrFun (siteAct_add i f g) xs

/-- The local physical Ward identity at any adjacent pair of contour wires. -/
theorem current_site_prefix (pre qs : List ℂ) (f : FState) :
    current (pre++1::r::qs) (siteAct pre.length f) =
      siteAct pre.length (current (pre++r::1::qs) f) := by
  induction pre generalizing f with
  | nil => exact current_site_zero qs f
  | cons q pre ih =>
    funext xs
    cases xs with
    | nil => simp [current,siteAct]
    | cons x xs =>
      simp only [List.cons_append,List.length_cons,current,siteAct]
      rw [ih]
      rw [siteAct_pointwise_add,siteAct_scalar]
      have h := siteAct_twist pre.length (fun ys=>∑ z, raising x z*f (z::ys)) xs
      rw [show (fun ys=>q*(∑ z, raising x z*f (z::ys))*twistProduct ys)=
          (fun ys=>q*(twistProduct ys*(∑ z, raising x z*f (z::ys)))) from by funext ys; ring,
        siteAct_scalar,h,siteAct_sum]
      simp only [siteAct_scalar]
      ring

noncomputable def rowAct : ℕ → ℕ → FState → FState
  | _, 0, f => f
  | i, n+1, f => rowAct (i+1) n (siteAct i f)

lemma rowAct_current (pre qs : List ℂ) (n : ℕ) (f : FState) :
    current (pre++List.replicate n 1++r::qs) (rowAct pre.length n f) =
      rowAct pre.length n (current (pre++r::(List.replicate n 1++qs)) f) := by
  induction n generalizing pre f with
  | zero => simp [rowAct]
  | succ n ih =>
    simp only [rowAct]
    have h := ih (pre++[1]) (siteAct pre.length f)
    simp only [List.length_append,List.length_singleton,List.append_assoc,
      List.cons_append,List.nil_append] at h
    rw [show pre++List.replicate (n+1) 1++r::qs=
        pre++1::(List.replicate n 1++r::qs) by simp [List.replicate_succ,List.append_assoc],h]
    have hlocal := current_site_prefix pre (List.replicate n 1++qs) f
    rw [hlocal]
    simp only [List.replicate_succ,List.cons_append]

noncomputable def rectangleAct : ℕ → ℕ → FState → FState
  | 0, _, f => f
  | w+1, h, f => rectangleAct w h (rowAct w h f)

/-- Finite rectangle current conservation, including all boundary indices.
It is an equality for the literal physical tensor network, not an assumed
bound or an infinite-volume assertion. -/
theorem rectangle_current (w h : ℕ) (qs : List ℂ) (f : FState) :
    current (List.replicate h 1 ++ List.replicate w r ++ qs) (rectangleAct w h f) =
      rectangleAct w h (current (List.replicate w r ++ List.replicate h 1 ++ qs) f) := by
  induction w generalizing qs f with
  | zero => simp [rectangleAct]
  | succ w ih =>
    have hw : List.replicate (w+1) r=List.replicate w r++[r] := by
      rw [List.replicate_add]; simp
    simp only [rectangleAct,hw,List.append_assoc,List.singleton_append]
    have hi := ih (r::qs) (rowAct w h f)
    simp only [List.append_assoc] at hi
    rw [hi]
    have hr := rowAct_current (List.replicate w r) qs h f
    simp only [List.length_replicate,List.append_assoc] at hr
    rw [hr]
    simp only [List.cons_append]


end CriticalHoneycomb.Transfer.FluxWard

namespace CriticalHoneycomb.Transfer.FluxWard
open scoped BigOperators Matrix

noncomputable def consState (a : Fin 3) (f : FState) : FState
  | [] => 0
  | x::xs => if x=a then f xs else 0
noncomputable def emptyState : FState
  | [] => 1
  | _::_ => 0
noncomputable def vacuum : ℕ → FState
  | 0 => emptyState
  | n+1 => consState 1 (vacuum n)
noncomputable def twistState (f : FState) : FState := fun xs=> twistProduct xs * f xs

lemma consState_add (a : Fin 3) (f g : FState) :
    consState a (f+g)=consState a f+consState a g := by
  funext xs
  cases xs <;> simp [consState] ; split <;> simp_all
lemma consState_smul (a : Fin 3) (z : ℂ) (f : FState) :
    consState a (z • f)=z • consState a f := by
  funext xs
  cases xs <;> simp [consState] 
lemma consState_zero (a : Fin 3) : consState a 0=0 := by
  ext xs; cases xs <;> simp [consState]

lemma current_zero (qs : List ℂ) : current qs (fun _=>0)=fun _=>0 :=
  (currentLinear qs).map_zero

lemma current_emptyHead (q : ℂ) (qs : List ℂ) (f : FState) :
    current (q::qs) (consState 1 f) =
      q • consState 0 (twistState f) + consState 1 (current qs f) := by
  funext xs
  cases xs with
  | nil => simp [current,consState]
  | cons x xs =>
    fin_cases x <;> simp [current,consState,twistState,raising,untwist,current_zero,mul_assoc,mul_comm]

lemma current_minusHead (q : ℂ) (qs : List ℂ) (f : FState) :
    current (q::qs) (consState 2 f) =
      (-q) • consState 1 (twistState f) + r^5 • consState 2 (current qs f) := by
  funext xs
  cases xs with
  | nil => simp [current,consState]
  | cons x xs =>
    fin_cases x <;> simp [current,consState,twistState,raising,untwist,current_zero,mul_assoc,mul_comm]

lemma twist_consState (a : Fin 3) (f : FState) :
    twistState (consState a f)=twist a • consState a (twistState f) := by
  ext xs
  cases xs with
  | nil => simp [consState,twistState]
  | cons x xs =>
    by_cases h : x=a
    · subst x; simp [twistState,twistProduct,consState,mul_assoc]
    · simp [twistState,consState,h]

lemma twist_vacuum (n : ℕ) : twistState (vacuum n)=vacuum n := by
  induction n with
  | zero => ext xs; cases xs <;> simp [vacuum,twistState,twistProduct,emptyState]
  | succ n ih => simp only [vacuum,twist_consState,ih]; simp [twist]

noncomputable def plusSum : List ℂ → FState
  | [] => 0
  | q::qs => q • consState 0 (vacuum qs.length)+consState 1 (plusSum qs)

lemma current_vacuum (qs : List ℂ) : current qs (vacuum qs.length)=plusSum qs := by
  induction qs with
  | nil => ext xs; rfl
  | cons q qs ih =>
    simp only [List.length_cons,vacuum,current_emptyHead,twist_vacuum,ih,plusSum]

noncomputable def prefixVac : ℕ → FState → FState
  | 0, f => f
  | n+1, f => consState 1 (prefixVac n f)
noncomputable def sourceState (pre post : ℕ) : FState :=
  prefixVac pre (consState 2 (vacuum post))

lemma prefixVac_add (n : ℕ) (f g : FState) : prefixVac n (f+g)=prefixVac n f+prefixVac n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [prefixVac,ih,consState_add]
lemma prefixVac_smul (n : ℕ) (z : ℂ) (f : FState) : prefixVac n (z • f)=z • prefixVac n f := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [prefixVac,ih,consState_smul]

lemma twist_source (pre post : ℕ) : twistState (sourceState pre post)=(-r^3) • sourceState pre post := by
  induction pre with
  | zero => simp [sourceState,prefixVac,twist_consState,twist_vacuum,twist]
  | succ pre ih =>
    change twistState (consState 1 (sourceState pre post))= _
    rw [twist_consState,ih,consState_smul]
    simp only [show twist 1=1 from rfl,one_smul]
    rfl

noncomputable def beforeArches : List ℂ → ℕ → FState
  | [], _ => 0
  | q::pre, post => q • consState 0 (sourceState pre.length post)+consState 1 (beforeArches pre post)
noncomputable def afterArches (pre : ℕ) (post : List ℂ) : FState :=
  prefixVac pre (consState 2 (plusSum post))

/-- The input side of the boundary Ward identity: the current creates just
one vacuum term and the two ordered classes of source-to-input arcs. -/
theorem current_source (pre post : List ℂ) (q : ℂ) :
    current (pre++q::post) (sourceState pre.length post.length) =
      (-q) • vacuum (pre.length+1+post.length) +
      (-r^3) • beforeArches pre post.length + r^5 • afterArches pre.length post := by
  induction pre with
  | nil =>
    simp only [List.nil_append,List.length_nil,sourceState,prefixVac,current_minusHead,
      twist_vacuum,current_vacuum,beforeArches,afterArches,smul_zero,add_zero]
    simp [vacuum,Nat.add_comm]
  | cons u pre ih =>
    change current (u::(pre++q::post)) (consState 1 (sourceState pre.length post.length)) = _
    rw [current_emptyHead,twist_source,consState_smul,ih]
    simp only [consState_add,consState_smul,List.length_cons,beforeArches,afterArches,prefixVac]
    rw [show pre.length+1+1+post.length=(pre.length+1+post.length)+1 by omega]
    simp only [vacuum,smul_add,smul_smul]
    module

noncomputable def exitSum : List ℂ → FState → ℂ
  | [], _ => 0
  | q::qs, f => q*f (2::List.replicate qs.length 1)+exitSum qs (fun xs=>f (1::xs))

lemma twistProduct_vacuum (n : ℕ) : twistProduct (List.replicate n 1)=1 := by
  simp [twistProduct,twist]

lemma current_vacuum_eval (qs : List ℂ) (f : FState) :
    current qs f (List.replicate qs.length 1) = -exitSum qs f := by
  induction qs generalizing f with
  | nil => simp [current,exitSum]
  | cons q qs ih =>
    simp only [List.length_cons,List.replicate_succ,current,exitSum]
    rw [ih,twistProduct_vacuum]
    simp [raising,untwist,add_comm]

lemma rowAct_add (i n : ℕ) (f g : FState) : rowAct i n (f+g)=rowAct i n f+rowAct i n g := by
  induction n generalizing i f g with
  | zero => rfl
  | succ n ih => simp only [rowAct,siteAct_add,ih]
lemma rowAct_smul (i n : ℕ) (z : ℂ) (f : FState) : rowAct i n (z • f)=z • rowAct i n f := by
  induction n generalizing i f with
  | zero => rfl
  | succ n ih => simp only [rowAct,siteAct_smul,ih]
lemma rectangleAct_add (w h : ℕ) (f g : FState) :
    rectangleAct w h (f+g)=rectangleAct w h f+rectangleAct w h g := by
  induction w generalizing f g with
  | zero => rfl
  | succ w ih => simp only [rectangleAct,rowAct_add,ih]
lemma rectangleAct_smul (w h : ℕ) (z : ℂ) (f : FState) :
    rectangleAct w h (z • f)=z • rectangleAct w h f := by
  induction w generalizing f with
  | zero => rfl
  | succ w ih => simp only [rectangleAct,rowAct_smul,ih]

/-- Exact boundary flux equality for a prescribed input port of the finite
physical lozenge rectangle. The three non-vacuum terms enumerate output
exits and the two contour-ordered classes of input-side arches. -/
theorem rectangle_boundary_flux (w h : ℕ) (pre post : List ℂ) (q : ℂ)
    (directions : List.replicate w r++List.replicate h 1=pre++q::post) :
    exitSum (List.replicate h 1++List.replicate w r)
        (rectangleAct w h (sourceState pre.length post.length)) +
      (-r^3)*(rectangleAct w h (beforeArches pre post.length)) (List.replicate (h+w) 1) +
      r^5*(rectangleAct w h (afterArches pre.length post)) (List.replicate (h+w) 1) =
      q*(rectangleAct w h (vacuum (w+h))) (List.replicate (h+w) 1) := by
  have len : pre.length+1+post.length=w+h := by
    have he := congrArg List.length directions
    simp only [List.length_append,List.length_replicate,List.length_cons] at he
    omega
  have hc := congrFun (rectangle_current w h [] (sourceState pre.length post.length))
    (List.replicate (h+w) 1)
  simp only [List.append_nil,directions] at hc
  rw [current_source,rectangleAct_add,rectangleAct_add,rectangleAct_smul,
    rectangleAct_smul,rectangleAct_smul,len] at hc
  rw [show h+w=(List.replicate h (1:ℂ)++List.replicate w r).length by simp] at hc
  rw [current_vacuum_eval] at hc
  simp only [List.length_append,List.length_replicate,Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hc
  linear_combination -hc


end CriticalHoneycomb.Transfer.FluxWard

/-!
Planar loop erasure for physical finite strips.
This implements the adjacent cup/cap contractions of the exact dilute
Temperley--Lieb tile. No physical partition-function estimate is assumed.
-/

namespace CriticalHoneycomb.Transfer.FluxWard
open scoped BigOperators Matrix
namespace Diagram
abbrev Spin := PlanarNormalization.Spin

def spinEquiv : Spin ≃ Fin 3 where
  toFun := PlanarNormalization.spinIndex
  invFun i := if i=1 then none else some (decide (i=2))
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl
noncomputable def physicalWeights : PlanarNormalization.TileWeights :=
  ⟨(kappa:ℂ),(kappa^2:ℂ),(kappa^2:ℂ),(kappa^2:ℂ),0⟩

lemma tile_physical (i j k l : Spin) :
    PlanarNormalization.tile physicalWeights i j k l =
      physicalTile (spinEquiv i) (spinEquiv j) (spinEquiv k) (spinEquiv l) := by
  rw [PlanarNormalization.tile_eq_sourceR]
  rfl

noncomputable def decode (f : FState) : PlanarNormalization.DiluteState :=
  fun xs=>f (xs.map spinEquiv)

lemma decode_siteAct (i : ℕ) (f : FState) :
    decode (siteAct i f)=PlanarNormalization.act physicalWeights i (decode f) := by
  induction i generalizing f with
  | zero =>
    funext xs
    cases xs with
    | nil => rfl
    | cons a xs => cases xs with
      | nil => rfl
      | cons b xs =>
        simp only [decode,List.map_cons,siteAct,PlanarNormalization.act,tile_physical]
        rw [←spinEquiv.sum_comp]
        apply Finset.sum_congr rfl
        intro s hs
        rw [←spinEquiv.sum_comp]
  | succ i ih =>
    funext xs
    cases xs with
    | nil => rfl
    | cons a xs =>
      change siteAct i (fun ys=>f (spinEquiv a::ys)) (xs.map spinEquiv) =
        PlanarNormalization.act physicalWeights i
          (decode (fun ys=>f (spinEquiv a::ys))) xs
      exact congrFun (ih (fun ys=>f (spinEquiv a::ys))) xs

lemma decode_vacuum (n : ℕ) : decode (vacuum n)=
    PlanarNormalization.embed (List.replicate n false) (fun _=>1) := by
  funext xs
  induction n generalizing xs with
  | zero => cases xs <;> simp [decode,vacuum,emptyState,PlanarNormalization.embed,PlanarNormalization.occupancy]
  | succ n ih =>
    cases xs with
    | nil => simp [decode,vacuum,consState,PlanarNormalization.embed,PlanarNormalization.occupancy]
    | cons x xs =>
      fin_cases x <;>
        simp [decode,vacuum,consState,spinEquiv,PlanarNormalization.spinIndex,
          PlanarNormalization.embed,PlanarNormalization.occupancy,List.replicate_succ] at ih ⊢
      exact ih xs

lemma decode_vacuum_eval (f : FState) (n : ℕ) :
    decode f (List.replicate n none)=f (List.replicate n 1) := by
  simp [decode,spinEquiv,PlanarNormalization.spinIndex]

lemma row_span {N i h : ℕ} (hi : i+h<N) {f : FState}
    (hf : PlanarNormalization.PlanarSpan N (decode f)) :
    PlanarNormalization.PlanarSpan N (decode (rowAct i h f)) := by
  induction h generalizing i f with
  | zero => exact hf
  | succ h ih =>
    apply ih (by omega)
    rw [decode_siteAct]
    exact PlanarNormalization.act_span physicalWeights (by omega) hf

lemma row_vacuum {N i h : ℕ} (hi : i+h<N) {f : FState}
    (hf : PlanarNormalization.PlanarSpan N (decode f)) :
    rowAct i h f (List.replicate N 1)=f (List.replicate N 1) := by
  induction h generalizing i f with
  | zero => rfl
  | succ h ih =>
    change rowAct (i+1) h (siteAct i f) _ = _
    have ha : PlanarNormalization.PlanarSpan N (decode (siteAct i f)) := by
      rw [decode_siteAct]
      exact PlanarNormalization.act_span physicalWeights (by omega) hf
    rw [ih (by omega) ha]
    have he := PlanarNormalization.act_vacuum physicalWeights (by omega : i+1<N) hf
    rw [←decode_siteAct,decode_vacuum_eval,decode_vacuum_eval] at he
    exact he

lemma rectangle_span {N w h : ℕ} (hi : w+h ≤ N) {f : FState}
    (hf : PlanarNormalization.PlanarSpan N (decode f)) :
    PlanarNormalization.PlanarSpan N (decode (rectangleAct w h f)) := by
  induction w generalizing f with
  | zero => exact hf
  | succ w ih =>
    apply ih (by omega)
    exact row_span (by omega) hf

lemma rectangle_vacuum {N w h : ℕ} (hi : w+h ≤ N) {f : FState}
    (hf : PlanarNormalization.PlanarSpan N (decode f)) :
    rectangleAct w h f (List.replicate N 1)=f (List.replicate N 1) := by
  induction w generalizing f with
  | zero => rfl
  | succ w ih =>
    change rectangleAct w h (rowAct w h f) _ = _
    rw [ih (by omega) (row_span (by omega) hf)]
    exact row_vacuum (by omega) hf

end Diagram

/-- The boundary Ward identity's normalization is the literal empty
partition: all detached closed honeycomb loops cancel. -/
theorem rectangle_vacuum_one (w h : ℕ) :
    rectangleAct w h (vacuum (w+h)) (List.replicate (h+w) 1)=1 := by
  have hs : PlanarNormalization.PlanarSpan (w+h) (Diagram.decode (vacuum (w+h))) := by
    rw [Diagram.decode_vacuum]
    exact PlanarNormalization.PlanarSpan.basis (List.replicate (w+h) false) 0 .start
      (by simp) (by simp [List.count_replicate])
  rw [show h+w=w+h by omega,Diagram.rectangle_vacuum (by omega) hs]
  have he := congrFun (Diagram.decode_vacuum (w+h)) (List.replicate (w+h) none)
  rw [Diagram.decode_vacuum_eval] at he
  simpa [PlanarNormalization.embed,PlanarNormalization.occupancy] using he

end CriticalHoneycomb.Transfer.FluxWard

end OAI
