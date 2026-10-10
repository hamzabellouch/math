import OAI.Analysis.PeriodicLattice.EffectivePotentials

namespace OAI

/-! Effective periodic velocity, pressure and solenoidal forces. -/

namespace PeriodicLattice

local instance finiteFunctionEncodingEffectiveForcing {n : ℕ} {A : Type*} [Encodable A] :
    Encodable (Fin n → A) := Encodable.finArrow

noncomputable section

namespace EffectiveFields
open CertifiedReal Quantitative RapidCalculus TorusCalculus RecursiveArithmetic
open scoped ContDiff
local instance effectiveForcingLocal1 : Primcodable ℚ := ratPrimcodable
local instance effectiveForcingLocal2 : DecidablePred Input.WellFormed := Classical.decPred _
local instance effectiveForcingLocal3 : Primcodable ValidInput := Primcodable.subtype inputWellFormed

theorem tensor_base {F : Input → ScalarField} {B : Input → ℝ → ℝ → ℝ} {h : ℝ → ℝ}
    (hb : Effective (fun p : ValidInput × BiPoint => biValue (B p.1.1) p.2))
    (hh : Effective (fun z : ℚ => h z))
    (heq : ∀ d t x, F d t (torusMk x) = h (x 2) * B d t (x 1)) :
    Effective (fun p : ValidInput × RationalPoint => fieldValue (F p.1.1) p.2) := by
  have ha : Computable (fun p : ValidInput × RationalPoint => (p.1,p.2.1,p.2.2 1)) :=
    (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
      (Primrec.fin_app.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 1)))).to_comp
  have hz : Computable (fun p : ValidInput × RationalPoint => p.2.2 2) :=
    (Primrec.fin_app.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 2)).to_comp
  exact ((hh.comp hz).mul (hb.comp ha)).congr (fun p => by
    dsimp only [fieldValue,biValue]
    rw [heq]
    rfl)

theorem phase_effective : Effective (fun z : ℚ => 2*Real.pi*((z:ℝ)-1/2)) := by
  have h := ((constant (A := ℚ) 2).mul pi).mul ((rational Computable.id).sub (constant (1/2)))
  simpa only [Rat.cast_ofNat,Rat.cast_div,Rat.cast_one,id_eq] using h

theorem eta_effective : Effective (fun z : ℚ => FluidLift.eta z) := by
  have hd : Effective (fun _ : ℚ => 2*Real.pi) := by simpa only [Rat.cast_ofNat] using (constant (A := ℚ) 2).mul pi
  exact phase_effective.sin.div hd (fun _ => mul_ne_zero (by norm_num) Real.pi_ne_zero)

theorem slope_effective : Effective (fun z : ℚ => FluidLift.slope z) := phase_effective.cos

theorem doubleSlope_effective : Effective (fun z : ℚ => FluidLift.doubleSlope z) := by
  exact (((constant (A := ℚ) 2).mul (slope_effective.mul slope_effective)).sub (constant 1)).congr
    (fun z => by simp only [FluidLift.doubleSlope,FluidLift.slope,Rat.cast_ofNat,Rat.cast_one]; ring)

theorem velocity_effective : ComponentsEffective FluidLift.velocity := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => i.elim0)))
  · exact tensor_base (F := fun d t q => FluidLift.velocity d t q 0) a_base slope_effective (fun d t x => by simp)
  · exact tensor_base (F := fun d t q => FluidLift.velocity d t q 1) b_base slope_effective (fun d t x => by simp)
  · exact tensor_base (F := fun d t q => FluidLift.velocity d t q 2) (h := fun z => -FluidLift.eta z) bdy_base eta_effective.neg (fun d t x => by simp)

theorem potential_effective : Effective (fun p : ValidInput × RationalPoint => fieldValue (FluidLift.potential p.1.1) p.2) := by
  have hbase : Effective (fun p : ValidInput × RationalPoint =>
      fieldValue (PeriodicInverse.horizontal (FluidLift.pressureBase p.1.1) (FluidLift.pressureBase_periodic p.1.1)) p.2) :=
    tensor_base (F := fun d => PeriodicInverse.horizontal (FluidLift.pressureBase d) (FluidLift.pressureBase_periodic d)) (h := fun _ => 1) pressureBase_base (by simpa only [Rat.cast_one] using (constant (A := ℚ) 1)) (fun d t x => by simp)
  exact hbase.add (tensor_base pressureMode_base doubleSlope_effective FluidLift.pressureOsc_cover)

theorem ComponentsEffective.diffusion {F : Input → VectorField} (hf : ComponentsEffective F)
    (hF : FieldCertificate F) : ComponentsEffective (fun d => laplacian (F d)) := by
  have hd (i) := (hf.diff hF (some i)).diff (hF.diff (some i)) (some i)
  intro j
  exact (((hd 0 j).add (hd 1 j)).add (hd 2 j)).congr (fun p => by
    simp only [laplacian,Fin.sum_univ_three,PiLp.add_apply,coordD])

theorem ComponentsEffective.transport {F : Input → VectorField} (hf : ComponentsEffective F)
    (hF : FieldCertificate F) : ComponentsEffective (fun d => advection (F d)) := by
  intro j
  exact ((((hf 0).mul (hf.diff hF (some 0) j)).add ((hf 1).mul (hf.diff hF (some 1) j))).add
    ((hf 2).mul (hf.diff hF (some 2) j))).congr (fun p => by
      simp only [advection,Fin.sum_univ_three,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,coordD])

theorem ComponentsEffective.gradient {F : Input → ScalarField}
    (hf : Effective (fun p : ValidInput × RationalPoint => fieldValue (F p.1.1) p.2))
    (hF : FieldCertificate F) : ComponentsEffective (fun d => gradient (F d)) :=
  fun i => field_diff hF hf (some i)

theorem force_effective (ν : ℝ) (hc : Effective (fun _ : Unit => ν)) : ComponentsEffective (FluidLift.force ν) :=
  ((velocity_effective.diff velocityCertificate none).add (velocity_effective.transport velocityCertificate)).sub
    ((velocity_effective.diffusion velocityCertificate).scale ν hc)

theorem solenoidalForce_effective (ν : ℝ) (hc : Effective (fun _ : Unit => ν)) : ComponentsEffective (FluidLift.solenoidalForce ν) :=
  (force_effective ν hc).sub (ComponentsEffective.gradient potential_effective potentialCertificate)

end EffectiveFields

namespace CertifiedReal
open RecursiveArithmetic
local instance effectiveForcingLocal4 : Primcodable ℚ := ratPrimcodable

theorem accuracy_as_inv (n : ℕ) : accuracy n = ((2:ℝ)^n)⁻¹ := by simp [accuracy,zpow_neg]

theorem accuracy_le_error (n : ℕ) : accuracy n ≤ error n := by
  rw [accuracy_as_inv,error,one_div]
  apply inv_le_inv₀ (by positivity) (by positivity) |>.mpr
  exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := n))

theorem computableReal_effective {x : ℝ} (hx : ComputableReal x) : Effective (fun _ : Unit => x) := by
  obtain ⟨P,hP⟩ := hx
  choose q hq he using hP
  have henc : Computable (fun n => Encodable.encode (q n)) :=
    (Nat.Partrec.Code.eval_part.comp (Computable.const P) Computable.id).of_eq_tot hq
  have hc : Computable q := Computable.encode_iff.mp henc
  exact ⟨fun p => q p.2,hc.comp Computable.snd,fun _ n => (he n).trans (accuracy_le_error n)⟩

end CertifiedReal
namespace EffectiveFields
open CertifiedReal Quantitative RapidCalculus TorusCalculus RecursiveArithmetic
open scoped ContDiff
local instance effectiveForcingLocal5 : Primcodable ℚ := ratPrimcodable
local instance effectiveForcingLocal6 : DecidablePred Input.WellFormed := Classical.decPred _
local instance effectiveForcingLocal7 : Primcodable ValidInput := Primcodable.subtype inputWellFormed

theorem time_error {t : ℝ} (ht : 0 ≤ t) (a : ℚ) : |t - time a| ≤ |t - (a:ℝ)| := by
  rw [time_eq]
  rcases le_total 0 (a:ℝ) with ha | ha
  · rw [max_eq_left ha]
  · rw [max_eq_right ha,sub_zero,abs_of_nonneg ht,abs_of_nonneg (by linarith : 0 ≤ t-(a:ℝ))]
    linarith

section Distance
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

theorem field_distance {F : Field A} (hF : ContDiff ℝ ∞ (lifted F))
    {K δ t s : ℝ} (hK : 0 ≤ K)
    (hb : ∀ i : Option (Fin 3), ∀ u : ℝ, 0 ≤ u → ∀ q, ‖coordD i F u q‖ ≤ K)
    (ht : 0 ≤ t) (hs : 0 ≤ s) (x y : Space)
    (hΔt : |t-s| ≤ δ) (hΔx : ∀ i, |x i-y i| ≤ δ) :
    ‖F t (torusMk x) - F s (torusMk y)‖ ≤ 4*K*δ := by
  have htime : ‖F t (torusMk x) - F s (torusMk x)‖ ≤ K*δ := by
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u _ => (fullTime_hasDerivAt hF u (torusMk x)).hasDerivWithinAt)
      (fun u hu => hb none u hu (torusMk x)) (convex_Ici (0:ℝ)) hs ht
    exact h.trans (mul_le_mul_of_nonneg_left hΔt hK)
  have hspace (z : Space) (i : Fin 3) :
      ‖F s (torusMk (z+EuclideanSpace.single i (x i-y i))) - F s (torusMk z)‖ ≤ K*δ := by
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := Set.univ)
      (fun u _ => (translation_hasDerivAt (smooth_slice_differentiable hF s) (torusMk z) i u).hasDerivWithinAt)
      (fun u _ => hb (some i) s hs (torusMk z+torusMk (EuclideanSpace.single i u)))
      convex_univ (Set.mem_univ (0:ℝ)) (Set.mem_univ (x i-y i))
    simp only [sub_zero,Real.norm_eq_abs,single_zero,mk_zero,add_zero,← mk_add] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hΔx i) hK)
  let z₁ := y+EuclideanSpace.single 0 (x 0-y 0)
  let z₂ := z₁+EuclideanSpace.single 1 (x 1-y 1)
  have hx : z₂+EuclideanSpace.single 2 (x 2-y 2) = x := by
    ext i
    fin_cases i <;> simp [z₂,z₁]
  have h₀ := hspace y 0
  have h₁ := hspace z₁ 1
  have h₂ := hspace z₂ 2
  rw [hx] at h₂
  calc
    _ ≤ ‖F t (torusMk x) - F s (torusMk x)‖ + ‖F s (torusMk x) - F s (torusMk y)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ K*δ + (‖F s (torusMk x) - F s (torusMk z₂)‖ + ‖F s (torusMk z₂) - F s (torusMk y)‖) :=
      add_le_add htime (norm_sub_le_norm_sub_add_norm_sub _ _ _)
    _ ≤ K*δ + (K*δ + (‖F s (torusMk z₂) - F s (torusMk z₁)‖ + ‖F s (torusMk z₁) - F s (torusMk y)‖)) :=
      add_le_add le_rfl (add_le_add h₂ (norm_sub_le_norm_sub_add_norm_sub _ _ _))
    _ ≤ K*δ + (K*δ + (K*δ+K*δ)) := by gcongr
    _ = _ := by ring

theorem fieldWord_nearby {F : Input → Field A} (hF : FieldCertificate F)
    (d : ValidInput) (w : List (Option (Fin 3))) (a : RationalPoint)
    {δ t : ℝ} (ht : 0 ≤ t) (x : Space)
    (hΔt : |t-(a.1:ℝ)| ≤ δ) (hΔx : ∀ i, |x i-(a.2 i:ℝ)| ≤ δ) :
    ‖fieldWord w (F d.1) t (torusMk x) - fieldWord w (F d.1) (time a.1) (torusMk (rationalVector a.2))‖ ≤
      4*(hF.budget (d.1,w.length+1,0):ℝ)*δ := by
  apply field_distance (fieldWord_contDiff (hF.smooth d.1) w) (Nat.cast_nonneg _) _ ht (time_nonneg a.1) x (rationalVector a.2)
    ((time_error ht a.1).trans hΔt) hΔx
  intro i u hu q
  simpa only [fieldWord_cons,pow_zero,one_mul] using
    hF.estimate d.1 d.2 (i::w) (w.length+1) 0 (by simp) u hu q
end Distance

theorem word_evaluator {F : Input → VectorField} (hF : FieldCertificate F) (hf : ComponentsEffective F) :
    ∃ Q : (ValidInput × List (Option (Fin 3)) × RationalPoint) × ℕ → Fin 3 → ℚ,
      Computable Q ∧ ∀ (d : ValidInput) w a n,
        ‖fieldWord w (F d.1) (time a.1) (torusMk (rationalVector a.2)) - rationalVector (Q ((d,w,a),n))‖ ≤ 3*error n := by
  have he (i : Fin 3) := field_words (hF.component i) (hf i)
  choose q hq bq using he
  let Q : (ValidInput × List (Option (Fin 3)) × RationalPoint) × ℕ → Fin 3 → ℚ := fun an i => q i an
  have hQ : Computable Q := (Primrec.vector_get'.to_comp.comp (Computable.vector_ofFn hq)).of_eq (fun an => by
    funext i
    simp only [List.Vector.get_ofFn]
    rfl)
  refine ⟨Q,hQ,fun d w a n => ?_⟩
  have hcoord (i : Fin 3) :
      ‖(fieldWord w (F d.1) (time a.1) (torusMk (rationalVector a.2)) - rationalVector (Q ((d,w,a),n))) i‖ ≤ error n := by
    change |fieldWord w (F d.1) (time a.1) (torusMk (rationalVector a.2)) i - (q i ((d,w,a),n):ℝ)| ≤ error n
    simpa only [fieldValue,fieldWord_component (hF.smooth d.1)] using bq i (d,w,a) n
  calc
    _ ≤ ∑ i : Fin 3, ‖(fieldWord w (F d.1) (time a.1) (torusMk (rationalVector a.2)) - rationalVector (Q ((d,w,a),n))) i‖ := norm_le_sum_components _
    _ ≤ ∑ _i : Fin 3, error n := Finset.sum_le_sum (fun i _ => hcoord i)
    _ = _ := by simp

end EffectiveFields
namespace CertifiedReal

theorem accuracy_pos (n : ℕ) : 0 < accuracy n := by unfold accuracy; positivity

theorem accuracy_add (n k : ℕ) : accuracy (n+k) = accuracy n * accuracy k := by
  simp only [accuracy_as_inv,pow_add,mul_inv]

theorem error_pow (n : ℕ) : error (2^n) ≤ accuracy n := by
  rw [error,accuracy_as_inv,one_div]
  apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
  simp only [Nat.cast_pow,Nat.cast_ofNat]
  linarith

theorem accuracy_budget (K : ℕ) : (K:ℝ)*accuracy K ≤ 1 := by
  rw [accuracy_as_inv,← div_eq_mul_inv]
  apply (div_le_iff₀ (by positivity)).mpr
  rw [one_mul]
  exact_mod_cast (Nat.lt_two_pow_self (n := K)).le

theorem evaluation_tolerance (n K : ℕ) :
    4*(K:ℝ)*accuracy (n+K+6) + 3*error (2^(n+6)) ≤ accuracy n := by
  have he : accuracy 6 = 1/64 := by norm_num [accuracy]
  have hK := mul_le_mul_of_nonneg_left (accuracy_budget K) (accuracy_pos n).le
  have hp : 0 < accuracy n := accuracy_pos n
  calc
    _ ≤ 4*(K:ℝ)*accuracy (n+K+6) + 3*accuracy (n+6) := by
      gcongr
      exact error_pow _
    _ ≤ _ := by
      simp only [accuracy_add,he]
      nlinarith
end CertifiedReal

end
end PeriodicLattice

end OAI
