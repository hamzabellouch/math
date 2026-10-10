import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.ElementaryJets
import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.TemporalJets

namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set Filter
open scoped Topology

lemma computable_fin_lam {α β : Type*} [Primcodable α] [Primcodable β]
    {n : ℕ} {f : α → Fin n → β} (hf : ∀ i, Computable (fun a => f a i)) :
    Computable f := by
  exact (Primrec.vector_get'.to_comp.comp (Computable.vector_ofFn hf)).of_eq
    (fun a => by funext i; simp)

def rationalNatFloor (q : ℚ) : ℕ := q.num.toNat / q.den

lemma computable_rationalNatFloor : Computable rationalNatFloor :=
  Primrec.nat_div.to_comp.comp (primrec_int_toNat.to_comp.comp computable_rat_num)
    computable_rat_den

lemma rationalNatFloor_eq {q : ℚ} (hq : 0 ≤ q) : rationalNatFloor q = ⌊q⌋₊ := by
  have hn : 0 ≤ q.num := Rat.num_nonneg.mpr hq
  have he : ((q.num.toNat : ℕ) : ℚ) / (q.den : ℚ) = q := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hn, Rat.num_div_den]
  conv_rhs => rw [← he, Rat.natFloor_natCast_div_natCast]
  rfl

lemma rationalNatFloor_cast {q : ℚ} (hq : 0 ≤ q) :
    (rationalNatFloor q : ℝ) = (⌊(q : ℝ)⌋ : ℤ) := by
  rw [Rat.floor_cast, rationalNatFloor_eq hq, ← Int.natCast_floor_eq_floor hq]
  simp

def rationalPhase (q : ℚ) : ℚ := if q < 1 then q else q - rationalNatFloor q

lemma computable_rationalPhase : Computable rationalPhase := by
  apply computable_ite (computable_rat_lt.comp Computable.id (Computable.const 1)) Computable.id
  exact computable_rat_sub.comp Computable.id
    (computable_rat_natCast.comp computable_rationalNatFloor)

lemma rationalPhase_cast (q : ℚ) (hq : 0 ≤ q) :
    (rationalPhase q : ℝ) = if (q : ℝ) < 1 then (q : ℝ) else (q : ℝ) - (⌊(q : ℝ)⌋ : ℤ) := by
  by_cases h : q < 1
  · have hr : (q : ℝ) < 1 := by exact_mod_cast h
    simp [rationalPhase,h,hr]
  · have hr : ¬ (q : ℝ) < 1 := by exact_mod_cast h
    simp [rationalPhase,h,hr,rationalNatFloor_cast hq]

lemma rationalPhase_bound (q : ℚ) (hq : 0 ≤ q) : |(rationalPhase q : ℝ)| ≤ 1 := by
  rw [rationalPhase_cast q hq]
  split_ifs with h
  · rw [abs_of_nonneg (by exact_mod_cast hq)]
    exact h.le
  · have hlo := Int.floor_le (q : ℝ)
    have hhi := Int.lt_floor_add_one (q : ℝ)
    rw [abs_of_nonneg (by linarith)]
    linarith

def fieldRationalArgs {d : ℕ} (p : Fin d → ℚ) (t : ℚ) (x : Fin 3 → ℚ) :
    Fin (4+d) → ℚ := Fin.addCases (Fin.cases t x) p

lemma fieldRationalArgs_cast {d : ℕ} (p : Fin d → ℚ) (t : ℚ) (x : Fin 3 → ℚ) :
    (fun i => (fieldRationalArgs p t x i : ℝ)) = fieldArgs (fun i => (p i : ℝ)) t (rationalSpace x) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun k => ?_) i
  · refine Fin.cases ?_ (fun l => ?_) j <;> simp [fieldRationalArgs, fieldArgs, rationalSpace]
  · simp [fieldRationalArgs, fieldArgs]

lemma computable_fieldRationalArgs (d : ℕ) :
    Computable (fun z : (Fin d → ℚ) × RationalPoint => fieldRationalArgs z.1 z.2.1 z.2.2) := by
  apply computable_fin_lam
  intro i
  refine Fin.addCases (fun j => ?_) (fun k => ?_) i
  · refine Fin.cases ?_ (fun l => ?_) j
    · simpa only [id_eq,fieldRationalArgs,Fin.addCases_left,Fin.cases_zero] using
        (Computable.fst.comp Computable.snd : Computable (fun z : (Fin d → ℚ) × RationalPoint => z.2.1))
    · simpa only [id_eq,fieldRationalArgs,Fin.addCases_left,Fin.cases_succ] using
        (Computable.fin_app.comp (Computable.snd.comp Computable.snd) (Computable.const l) :
          Computable (fun z : (Fin d → ℚ) × RationalPoint => z.2.2 l))
  · simpa only [id_eq,fieldRationalArgs,Fin.addCases_right] using
      (Computable.fin_app.comp Computable.fst (Computable.const k) :
        Computable (fun z : (Fin d → ℚ) × RationalPoint => z.1 k))

lemma fieldArgs_bound {d : ℕ} (p : Fin d → ℝ) (t : ℝ) (x : Space) (C S : ℕ)
    (hp : ∀ i, |p i| ≤ C) (ht : |t| ≤ 1) (hx : ∀ i, |x i| ≤ S) :
    ∀ j, |fieldArgs p t x j| ≤ (C+1+S : ℕ) := by
  intro j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · refine Fin.cases ?_ (fun i => ?_) k
    · change |t| ≤ _; push_cast; linarith [Nat.cast_nonneg C (α := ℝ), Nat.cast_nonneg S (α := ℝ)]
    · simp only [fieldArgs,Fin.append_left,Fin.cons_succ]; push_cast; linarith [hx i, Nat.cast_nonneg C (α := ℝ)]
  · simp only [fieldArgs,Fin.append_right]; push_cast; linarith [hp k, Nat.cast_nonneg S (α := ℝ)]

def ElementaryPieces {d : ℕ} (L V : (Fin d → ℝ) → Velocity)
    (κ : ℕ → Fin d → ℚ) (F : Family Velocity) : Prop :=
  ∀ M w t, 0 ≤ t →
    if t < 1 then
      F M w =ᶠ[𝓝 t] L (fun i => (κ (inputCode M w) i : ℝ))
    else F M w =ᶠ[𝓝 t]
      (fun s => V (fun i => (κ (inputCode M w) i : ℝ)) (s - (⌊t⌋ : ℤ)))

lemma ElementaryPieces.jet {d : ℕ} {L V : (Fin d → ℝ) → Velocity}
    {κ : ℕ → Fin d → ℚ} {F : Family Velocity} (h : ElementaryPieces L V κ F)
    (M : FiniteMachine) (w : Input M) (a : MultiIndex) (t : ℝ) (ht : 0 ≤ t) (x : Space) :
    fullMixedD a (F M w) t x =
      if t < 1 then fullMixedD a (L (fun i => (κ (inputCode M w) i : ℝ))) t x
      else fullMixedD a (V (fun i => (κ (inputCode M w) i : ℝ))) (t - (⌊t⌋ : ℤ)) x := by
  have hh := h M w t ht
  split_ifs at hh ⊢ with hlt
  · exact congrFun (timeGerm_fullMixedD hh a |>.self_of_nhds) x
  · simpa only [fullMixedD_translate] using
      (congrFun (timeGerm_fullMixedD hh a |>.self_of_nhds) x)

lemma computable_sum_nat {α ι : Type*} [Primcodable α] (s : Finset ι)
    {f : ι → α → ℕ} (hf : ∀ i ∈ s, Computable (f i)) :
    Computable (fun a => ∑ i ∈ s, f i a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Computable.const (0 : ℕ) : Computable (fun _ : α => 0))
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      Primrec.nat_add.to_comp.comp (hf i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

def gridRadius (C : ℕ) (x : Fin 3 → ℚ) : ℕ := C + 1 + ∑ i, (x i).num.natAbs

lemma computable_gridRadius (C : ℕ) : Computable (gridRadius C) := by
  apply Primrec.nat_add.to_comp.comp (Computable.const (C+1))
  apply computable_sum_nat
  intro i _
  exact primrec_int_natAbs.to_comp.comp (computable_rat_num.comp
    (Computable.fin_app.comp Computable.id (Computable.const i)))

lemma gridRadius_bound {d : ℕ} (p : Fin d → ℚ) (t : ℚ) (x : Fin 3 → ℚ) (C : ℕ)
    (hp : ∀ i, |(p i : ℝ)| ≤ C) (ht : |(t : ℝ)| ≤ 1) :
    ∀ j, |(fieldRationalArgs p t x j : ℝ)| ≤ gridRadius C x := by
  intro j
  rw [congrFun (fieldRationalArgs_cast p t x) j]
  apply fieldArgs_bound _ _ _ C _ hp ht _ j
  intro i
  exact (rat_abs_le_num (x i)).trans (by exact_mod_cast
    (Finset.single_le_sum (fun j _ => Nat.zero_le ((x j).num.natAbs)) (Finset.mem_univ i)))

theorem elementary_jet_evaluators {d : ℕ} {v : (Fin d → ℝ) → Velocity}
    (hv : ElementaryField v) (hs : ∀ p, JointSmooth (v p))
    {κ : ℕ → Fin d → ℚ} (hκ : Computable κ) (C : ℕ)
    (hC : ∀ n i, |(κ n i : ℝ)| ≤ C) :
    ∃ E : (ℕ × MultiIndex × RationalPoint × ℕ) → Fin 3 → ℚ,
    ∃ b : MultiIndex × ℕ → ℕ,
      Computable E ∧ Computable b ∧
      (∀ m a z n, |(z.1 : ℝ)| ≤ 1 → ∀ i,
        |(E (m,a,z,n) i : ℝ) - fullMixedD a (v (fun j => (κ m j : ℝ)))
          z.1 (rationalSpace z.2) i| ≤ error n) ∧
      (∀ m a t x (S : ℕ), |t| ≤ 1 → ‖x‖ ≤ (S : ℝ) →
        ‖fullMixedD a (v (fun j => (κ m j : ℝ))) t x‖ ≤ (b (a,S) : ℝ)) := by
  obtain ⟨ps,hps⟩ := elementary_jet_programs hv hs
  let E : (ℕ × MultiIndex × RationalPoint × ℕ) → Fin 3 → ℚ := fun z i =>
    (NumericProgram.fieldJet d z.2.1 (ps i)).approximation (gridRadius C z.2.2.1.2)
      (fieldRationalArgs (κ z.1) z.2.2.1.1 z.2.2.1.2) z.2.2.2
  let b : MultiIndex × ℕ → ℕ := fun z =>
    ∑ i, ((NumericProgram.fieldJet d z.1 (ps i)).bound (C+1+z.2)).1
  have hE : Computable E := by
    apply computable_fin_lam
    intro i
    let A := ℕ × MultiIndex × RationalPoint × ℕ
    have hp : Computable (fun z : A => NumericProgram.fieldJet d z.2.1 (ps i)) :=
      (NumericProgram.computable_fieldJet d).comp
        ((Computable.fst.comp Computable.snd).pair (Computable.const (ps i)))
    have hc : Computable (fun z : A => gridRadius C z.2.2.1.2) :=
      (computable_gridRadius C).comp (Computable.snd.comp
        (Computable.fst.comp (Computable.snd.comp Computable.snd)))
    have hx : Computable (fun z : A => fieldRationalArgs (κ z.1) z.2.2.1.1 z.2.2.1.2) :=
      Computable.comp (f := fun z : (Fin d → ℚ) × RationalPoint => fieldRationalArgs z.1 z.2.1 z.2.2)
        (g := fun z : A => (κ z.1,z.2.2.1)) (computable_fieldRationalArgs d)
        ((hκ.comp Computable.fst).pair (Computable.fst.comp (Computable.snd.comp Computable.snd)))
    have hn : Computable (fun z : A => z.2.2.2) :=
      Computable.snd.comp (Computable.snd.comp Computable.snd)
    exact Computable.comp
      (f := fun z : NumericProgram × ℕ × (Fin (4+d) → ℚ) × ℕ =>
        z.1.approximation z.2.1 z.2.2.1 z.2.2.2)
      (g := fun z : A => (NumericProgram.fieldJet d z.2.1 (ps i), gridRadius C z.2.2.1.2,
        fieldRationalArgs (κ z.1) z.2.2.1.1 z.2.2.1.2, z.2.2.2))
      (NumericProgram.computable_approximation (4+d)) (hp.pair (hc.pair (hx.pair hn)))
  have hb : Computable b := by
    apply computable_sum_nat
    intro i _
    have hp : Computable (fun z : MultiIndex × ℕ => NumericProgram.fieldJet d z.1 (ps i)) :=
      (NumericProgram.computable_fieldJet d).comp
        (Computable.fst.pair (Computable.const (ps i)))
    have hc : Computable (fun z : MultiIndex × ℕ => C+1+z.2) :=
      Primrec.nat_add.to_comp.comp (Computable.const (C+1)) Computable.snd
    exact Computable.fst.comp (NumericProgram.computable_bound.comp hp hc)
  refine ⟨E,b,hE,hb,?_,?_⟩
  · intro m a z n ht i
    have hh := hps i a (fieldArgs (fun j => (κ m j : ℝ)) z.1 (rationalSpace z.2))
    simp only [fieldParam_args,fieldTime_args,fieldSpace_args] at hh
    have he := (NumericProgram.fieldJet d a (ps i)).approximation_spec (gridRadius C z.2)
      (fieldRationalArgs (κ m) z.1 z.2) n (gridRadius_bound _ _ _ C (hC m) ht)
      (by rw [fieldRationalArgs_cast]; exact hh.1)
    rw [fieldRationalArgs_cast, hh.2] at he
    exact he
  · intro m a t x S ht hx
    apply (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg (b (a,S)))).mpr
    intro i
    rw [Real.norm_eq_abs]
    have hh := hps i a (fieldArgs (fun j => (κ m j : ℝ)) t x)
    simp only [fieldParam_args,fieldTime_args,fieldSpace_args] at hh
    have hi : ∀ i, |x i| ≤ S := fun i =>
      (le_trans (norm_le_pi_norm x i) hx)
    have he := (NumericProgram.fieldJet d a (ps i)).magnitude (C+1+S)
      (fieldArgs (fun j => (κ m j : ℝ)) t x)
      (fieldArgs_bound _ _ _ C S (hC m) ht hi) hh.1
    rw [hh.2] at he
    exact he.trans (by exact_mod_cast
      (Finset.single_le_sum (fun j _ => Nat.zero_le
        ((NumericProgram.fieldJet d a (ps j)).bound (C+1+S)).1) (Finset.mem_univ i)))

theorem effectiveFamily_of_elementary_pieces {d : ℕ}
    {L V : (Fin d → ℝ) → Velocity} (hL : ElementaryField L) (hV : ElementaryField V)
    (hsL : ∀p, JointSmooth (L p)) (hsV : ∀p, JointSmooth (V p))
    {κ : ℕ → Fin d → ℚ} (hκ : Computable κ) (C R : ℕ)
    (hC : ∀n i, |(κ n i : ℝ)| ≤ C) {F : Family Velocity}
    (hF : ∀M w, JointSmooth (F M w))
    (hS : ∀M w, SpatiallySupported (Metric.closedBall (0 : Space) R) (F M w))
    (hp : ElementaryPieces L V κ F) : EffectiveFamily F := by
  obtain ⟨EL,bL,hEL,hbL,heL,hmL⟩ := elementary_jet_evaluators hL hsL hκ C hC
  obtain ⟨EV,bV,hEV,hbV,heV,hmV⟩ := elementary_jet_evaluators hV hsV hκ C hC
  let phaseInput : (ℕ × MultiIndex × RationalPoint × ℕ) →
      (ℕ × MultiIndex × RationalPoint × ℕ) :=
    fun z => (z.1,z.2.1,(rationalPhase z.2.2.1.1,z.2.2.1.2),z.2.2.2)
  have hc : Computable phaseInput := by
    dsimp only [phaseInput]
    exact Computable.fst.pair ((Computable.fst.comp Computable.snd).pair
      (((computable_rationalPhase.comp (Computable.fst.comp
        (Computable.fst.comp (Computable.snd.comp Computable.snd)))).pair
        (Computable.snd.comp (Computable.fst.comp (Computable.snd.comp Computable.snd)))).pair
        (Computable.snd.comp (Computable.snd.comp Computable.snd))))
  let E : (ℕ × MultiIndex × RationalPoint × ℕ) → Fin 3 → ℚ :=
    fun z => if z.2.2.1.1 < 1 then EL (phaseInput z) else EV (phaseInput z)
  have hE : Computable E :=
    computable_ite (computable_rat_lt.comp (Computable.fst.comp
      (Computable.fst.comp (Computable.snd.comp Computable.snd))) (Computable.const 1))
      (hEL.comp hc) (hEV.comp hc)
  let b : ℕ × MultiIndex → ℕ := fun z => bL (z.2,R) + bV (z.2,R)
  have hb : Computable b := Primrec.nat_add.to_comp.comp
    (hbL.comp (Computable.snd.pair (Computable.const R)))
    (hbV.comp (Computable.snd.pair (Computable.const R)))
  refine ⟨E,b,(fun _ => R),hE,hb,Computable.const R,?_,?_,?_⟩
  · intro M w a z n hz i
    have ht : 0 ≤ (z.1 : ℝ) := by exact_mod_cast hz
    rw [← fullMixedD_eq_mixedD (hF M w) a _ ht _, hp.jet M w a _ ht _]
    dsimp only [E,phaseInput]
    by_cases hz' : z.1 < 1
    · have hr : (z.1 : ℝ) < 1 := by exact_mod_cast hz'
      simp only [ite_eq_left hz',ite_eq_left hr]
      have he := heL (inputCode M w) a (rationalPhase z.1,z.2) n
        (rationalPhase_bound _ hz) i
      simpa only [rationalPhase,ite_eq_left hz'] using he
    · have hr : ¬(z.1 : ℝ) < 1 := by exact_mod_cast hz'
      simp only [ite_eq_right hz',ite_eq_right hr]
      have he := heV (inputCode M w) a (rationalPhase z.1,z.2) n
        (rationalPhase_bound _ hz) i
      simpa only [rationalPhase_cast _ hz,ite_eq_right hr] using he
  · intro M w a t ht x
    rw [← fullMixedD_eq_mixedD (hF M w) a _ ht _]
    by_cases hx : ‖x‖ ≤ (R : ℝ)
    · rw [hp.jet M w a t ht x]
      split_ifs with hlt
      · have he := hmL (inputCode M w) a t x R
          (by rw [abs_of_nonneg ht]; exact hlt.le) hx
        exact he.trans (by dsimp [b]; push_cast; exact le_add_of_nonneg_right (Nat.cast_nonneg _))
      · have hlo := Int.floor_le t
        have hhi := Int.lt_floor_add_one t
        have he := hmV (inputCode M w) a (t-(⌊t⌋ : ℤ)) x R
          (by rw [abs_of_nonneg (by linarith)]; linarith) hx
        exact he.trans (by dsimp [b]; push_cast; exact le_add_of_nonneg_left (Nat.cast_nonneg _))
    · have he := (hS M w).fullMixedD Metric.isClosed_closedBall a t x
        (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)
      rw [he, norm_zero]
      exact Nat.cast_nonneg _
  · intro M w t _ x hx
    exact hS M w t x (by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx)

end BalancedTransport.Effectivity
end

end OAI
