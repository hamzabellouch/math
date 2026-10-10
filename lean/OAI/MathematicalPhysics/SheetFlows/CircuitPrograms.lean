import Mathlib
import OAI.MathematicalPhysics.SheetFlows.Circuits

namespace OAI

/-! SheetFlows circuit programs. -/

section
open Encodable Denumerable
namespace Solenoidal.Computing
open Nat.Partrec

theorem atom_argument : Primrec₂ Atom.argument :=
  rat_add.comp
    (rat_mul.comp (Primrec.fst.comp (Primrec.snd.comp .fst))
      (Primrec.fin_app.comp .snd (Primrec.fst.comp .fst)))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp .fst)))

theorem atom_bound : Primrec₂ Atom.bound := by
  let k : Atom×ℚ → ℕ := fun p => p.1.2.2.2
  have hk : Primrec k := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp .fst))
  exact Primrec.ite (Primrec.eq.comp hk (.const 0))
    (rat_add.comp (rat_mul.comp (rat_abs.comp (Primrec.fst.comp (Primrec.snd.comp .fst)))
        (rat_abs.comp .snd)) (rat_abs.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp .fst)))))
    (Primrec.ite (Primrec.eq.comp hk (.const 1)) (.const 16)
      (rat_nat.comp (nat_factorial.comp (Primrec.nat_sub.comp hk (.const 2)))))

theorem atom_approx : Primrec (fun p : Atom × (Fin 4 → ℚ) × ℕ => Atom.approx p.1 p.2.1 p.2.2) := by
  let k : Atom×(Fin 4 → ℚ)×ℕ → ℕ := fun p => p.1.2.2.2
  have hk : Primrec k := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp .fst))
  have hq : Primrec (fun p : Atom×(Fin 4 → ℚ)×ℕ => Atom.argument p.1 p.2.1) :=
    atom_argument.comp Primrec.fst (Primrec.fst.comp Primrec.snd)
  have hn : Primrec (fun p : Atom×(Fin 4 → ℚ)×ℕ => p.2.2) := Primrec.snd.comp .snd
  exact Primrec.ite (Primrec.eq.comp hk (.const 0)) (ball_point.comp hq)
    (Primrec.ite (Primrec.eq.comp hk (.const 1)) (ball_reciprocalApprox.comp hq hn)
      (ball_flatApprox.comp ((Primrec.nat_sub.comp hk (.const 2)).pair (hq.pair hn))))

theorem circuit_data {α : Type*} [Primcodable α] [Inhabited α] :
    Primrec (@Circuit.data α _ _) :=
  Primrec.option_getD_default.comp (Primrec.decode.comp Primrec.encode)

theorem circuit_const : Primrec Circuit.const :=
  Code.primrec_rfind'.comp ((Primrec.ofNat Code).comp Primrec.encode)

theorem circuit_atom : Primrec Circuit.atom :=
  Code.primrec₂_prec.comp ((Primrec.ofNat Code).comp Primrec.encode) (.const Code.zero)

theorem circuit_add : Primrec₂ Circuit.add := Code.primrec₂_pair
theorem circuit_mul : Primrec₂ Circuit.mul := Code.primrec₂_comp
theorem circuit_sub : Primrec₂ Circuit.sub :=
  circuit_add.comp .fst (circuit_mul.comp (.const (Circuit.const (-1))) .snd)

theorem circuit_bound : Primrec₂ Circuit.bound := by
  have h := Code.primrec_recOn' (α := Circuit×ℚ) (σ := ℚ) Primrec.fst
    (Primrec.const 0) (Primrec.const 0) (Primrec.const 0) (Primrec.const 0)
    (rat_add.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp .snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp .snd)))).to₂
    (rat_mul.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp .snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp .snd)))).to₂
    (atom_bound.comp (circuit_data.comp (Primrec.fst.comp .snd)) (Primrec.snd.comp .fst)).to₂
    (rat_abs.comp (circuit_data.comp (Primrec.fst.comp .snd))).to₂
  exact h.of_eq (fun p => by
    induction p.1 with
    | zero | succ | left | right => rfl
    | pair a b ha hb => simp [Circuit.bound,ha,hb]
    | comp a b ha hb => simp [Circuit.bound,ha,hb]
    | prec a b ha hb => rfl
    | rfind' a ha => rfl)

theorem circuit_approx : Primrec (fun p : Circuit×(Fin 4 → ℚ)×ℕ => Circuit.approx p.1 p.2.1 p.2.2) := by
  have h := Code.primrec_recOn' (α := Circuit×(Fin 4 → ℚ)×ℕ) (σ := QBall) Primrec.fst
    (Primrec.const (QBall.point 0)) (Primrec.const (QBall.point 0))
    (Primrec.const (QBall.point 0)) (Primrec.const (QBall.point 0))
    (ball_add.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp .snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp .snd)))).to₂
    (ball_mul.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp .snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp .snd)))).to₂
    (atom_approx.comp ((circuit_data.comp (Primrec.fst.comp .snd)).pair (Primrec.snd.comp .fst))).to₂
    (ball_point.comp (circuit_data.comp (Primrec.fst.comp .snd))).to₂
  exact h.of_eq (fun p => by
    induction p.1 with
    | zero | succ | left | right => rfl
    | pair a b ha hb => simp [Circuit.approx,ha,hb]
    | comp a b ha hb => simp [Circuit.approx,ha,hb]
    | prec a b ha hb => rfl
    | rfind' a ha => rfl)

theorem atom_withKind : Primrec₂ Atom.withKind :=
  (Primrec.fst.comp .fst).pair ((Primrec.fst.comp (Primrec.snd.comp .fst)).pair
    ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp .fst))).pair .snd))

theorem atom_reflect : Primrec Atom.reflect :=
  Primrec.fst.pair ((rat_neg.comp (Primrec.fst.comp .snd)).pair
    ((rat_sub.comp (.const 1) (Primrec.fst.comp (Primrec.snd.comp .snd))).pair
      (Primrec.snd.comp (Primrec.snd.comp .snd))))

theorem circuit_atomDiff : Primrec₂ Circuit.atomDiff := by
  let k : Fin 4×Atom → ℕ := fun p => p.2.2.2.2
  have hk : Primrec k := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp .snd))
  have hat (f : Fin 4×Atom → Atom) (hf : Primrec f) (n : Fin 4×Atom → ℕ) (hn : Primrec n) :
      Primrec (fun p => Circuit.atom ((f p).withKind (n p))) :=
    circuit_atom.comp (atom_withKind.comp hf hn)
  exact Primrec.ite (Primrec.eq.comp (Primrec.fst.comp .snd) .fst)
    (circuit_mul.comp (circuit_const.comp (Primrec.fst.comp (Primrec.snd.comp .snd)))
      (Primrec.ite (Primrec.eq.comp hk (.const 0)) (.const (Circuit.const 1))
        (Primrec.ite (Primrec.eq.comp hk (.const 1))
          (circuit_mul.comp (.const (Circuit.const (-1)))
            (circuit_mul.comp (circuit_mul.comp (circuit_atom.comp .snd) (circuit_atom.comp .snd))
              (circuit_sub.comp (hat _ .snd _ (.const 4))
                (hat _ (atom_reflect.comp .snd) _ (.const 4)))))
          (circuit_sub.comp
            (hat _ .snd _ (Primrec.nat_add.comp (Primrec.nat_sub.comp hk (.const 2)) (.const 4)))
            (circuit_mul.comp (circuit_const.comp (rat_nat.comp (Primrec.nat_sub.comp hk (.const 2))))
              (hat _ .snd _ (Primrec.nat_add.comp (Primrec.nat_sub.comp hk (.const 2)) (.const 3))))))))
    (.const (Circuit.const 0))

theorem circuit_diff : Primrec₂ Circuit.diff := by
  have h := Code.primrec_recOn' (α := Fin 4×Circuit) (σ := Circuit) Primrec.snd
    (Primrec.const (Circuit.const 0)) (Primrec.const (Circuit.const 0))
    (Primrec.const (Circuit.const 0)) (Primrec.const (Circuit.const 0))
    (circuit_add.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp .snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp .snd)))).to₂
    (circuit_add.comp
      (circuit_mul.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp .snd)))
        (Primrec.fst.comp (Primrec.snd.comp .snd)))
      (circuit_mul.comp (Primrec.fst.comp .snd)
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp .snd))))).to₂
    (circuit_atomDiff.comp (Primrec.fst.comp .fst) (circuit_data.comp (Primrec.fst.comp .snd))).to₂
    (Primrec₂.const (Circuit.const 0))
  exact h.of_eq (fun p => by
    induction p.2 with
    | zero | succ | left | right => rfl
    | pair a b ha hb => simp [Circuit.diff,ha,hb]
    | comp a b ha hb => simp [Circuit.diff,ha,hb]
    | prec a b ha hb => rfl
    | rfind' a ha => rfl)

theorem circuit_mixed : Primrec₂ Circuit.mixed := by
  have h := Primrec.list_foldr (α := Circuit×List (Fin 4)) Primrec.snd Primrec.fst
    (circuit_diff.comp (Primrec.fst.comp .snd) (Primrec.snd.comp .snd)).to₂
  exact h.of_eq (fun p => by
    induction p.2 with
    | nil => rfl
    | cons j a ha => simp [Circuit.mixed,List.foldr,ha])

end Solenoidal.Computing
end

open Set Filter Encodable
open scoped BigOperators Topology
namespace Solenoidal

def HasCircuit (u : Field) : Prop := ∃ e : Fin 3 → Circuit,
  Set.EqOn (fun z => u z.1 z.2) (fun z => Circuit.field e z.1 z.2) closedPeriodCell

theorem HasRationalFormula.circuit {u : Field} (h : HasRationalFormula u) : HasCircuit u := by
  obtain ⟨e,he⟩ := h
  refine ⟨fun j => BoxExpr.compile (e j), ?_⟩
  intro z hz
  rw [he hz]
  ext j
  exact (BoxExpr.compile_correct (e j) z).symm

namespace Circuit

def jetBound (e : Fin 3 → Circuit) (a : List (Fin 4)) : ℚ :=
  ∑ j, bound (mixed (e j) a) 10

theorem jetBound_nonneg (e : Fin 3 → Circuit) (a : List (Fin 4)) : 0 ≤ jetBound e a :=
  Finset.sum_nonneg (fun _ _ => bound_nonneg _ _)

theorem jetBound_correct (e : Fin 3 → Circuit) (a : List (Fin 4)) (z : SpaceTime)
    (hz : ∀ j, |coordinateLinear j z| ≤ 10) :
    ‖mixedDerivative (field e) a z‖ ≤ (jetBound e a : ℝ) := by
  apply (pi_norm_le_iff_of_nonneg (by exact_mod_cast jetBound_nonneg e a)).mpr
  intro j
  rw [mixed_field]
  change |eval (mixed (e j) a) z| ≤ _
  apply (bound_correct _ 10 z (by simpa using hz)).trans
  exact_mod_cast Finset.single_le_sum (fun i _ => bound_nonneg _ _) (Finset.mem_univ j)

def wrapRat (q : Fin 4 → ℚ) : Fin 4 → ℚ := fun j =>
  let T : ℚ := if j=0 then 1 else 10
  T * Int.fract (q j / T)

theorem wrapRat_correct (q : Fin 4 → ℚ) : ofRational (wrapRat q) =
    (Int.fract (ofRational q).1,wrapSpace (ofRational q).2) := by
  apply Prod.ext
  · simp [ofRational,wrapRat,Rat.cast_fract]
  · ext j
    fin_cases j <;> simp [ofRational,wrapRat,wrapSpace,Rat.cast_fract]

def jetApprox (e : Fin 3 → Circuit) (a : List (Fin 4)) (q : Fin 4 → ℚ) (n : ℕ) : Fin 3 → QBall :=
  fun j => approx (mixed (e j) a) (wrapRat q) n

end Circuit

theorem circuit_periodic_jet {u : Field} (hu : Smooth u) (hx : SpatiallyPeriodic u)
    (ht : OnePeriodic u) {e : Fin 3 → Circuit}
    (he : Set.EqOn (fun z => u z.1 z.2) (fun z => Circuit.field e z.1 z.2) closedPeriodCell)
    (a : List (Fin 4)) (z : SpaceTime) :
    mixedDerivative u a z = mixedDerivative (Circuit.field e) a (Int.fract z.1,wrapSpace z.2) := by
  have hp := periodic_field_reduction
    (mixedDerivative_spatially_periodic hu hx a) (mixedDerivative_onePeriodic hu ht a) z.1 z.2
  change mixedDerivative u a z = mixedDerivative u a (Int.fract z.1,wrapSpace z.2) at hp
  rw [hp]
  exact mixedDerivative_eqOn_cell hu (Circuit.field_smooth e) he a
    ⟨⟨Int.fract_nonneg _,(wrapSpace_mem z.2).1⟩,
      ⟨(Int.fract_lt_one _).le,(wrapSpace_mem z.2).2⟩⟩

theorem circuit_periodic_bound {u : Field} (hu : Smooth u) (hx : SpatiallyPeriodic u)
    (ht : OnePeriodic u) {e : Fin 3 → Circuit}
    (he : Set.EqOn (fun z => u z.1 z.2) (fun z => Circuit.field e z.1 z.2) closedPeriodCell)
    (a : List (Fin 4)) (z : SpaceTime) :
    ‖mixedDerivative u a z‖ ≤ (Circuit.jetBound e a : ℝ) := by
  rw [circuit_periodic_jet hu hx ht he]
  apply Circuit.jetBound_correct
  intro j
  fin_cases j
  · change |Int.fract z.1| ≤ 10
    rw [abs_of_nonneg (Int.fract_nonneg _)]
    exact (Int.fract_lt_one _).le.trans (by norm_num)
  all_goals
    change |wrapSpace z.2 _| ≤ 10
    rw [abs_of_nonneg ((wrapSpace_mem z.2).1 _)]
    exact (wrapSpace_mem z.2).2 _

theorem circuit_periodic_approx {u : Field} (hu : Smooth u) (hx : SpatiallyPeriodic u)
    (ht : OnePeriodic u) {e : Fin 3 → Circuit}
    (he : Set.EqOn (fun z => u z.1 z.2) (fun z => Circuit.field e z.1 z.2) closedPeriodCell)
    (a : List (Fin 4)) (q : Fin 4 → ℚ) (j : Fin 3) :
    QBall.Approximates (fun n => Circuit.jetApprox e a q n j)
      (mixedDerivative u a (Circuit.ofRational q) j) := by
  rw [circuit_periodic_jet hu hx ht he, Circuit.mixed_field,← Circuit.wrapRat_correct]
  exact Circuit.approximates _ _

namespace Computing

theorem fin_sum_rat {α : Type*} [Primcodable α] {n : ℕ} {f : α → Fin n → ℚ}
    (hf : ∀ i, Primrec (fun a => f a i)) : Primrec (fun a => ∑ i, f a i) := by
  induction n with
  | zero => simpa using (Primrec.const (0:ℚ) : Primrec (fun _ : α => (0:ℚ)))
  | succ n ih =>
    simpa [Fin.sum_univ_succ] using rat_add.comp (hf 0) (ih (fun i => hf i.succ))

theorem circuit_jetBound (e : Fin 3 → Circuit) : Primrec (Circuit.jetBound e) :=
  fin_sum_rat (fun j => circuit_bound.comp (circuit_mixed.comp (.const (e j)) .id) (.const 10))

theorem circuit_wrapRat : Primrec Circuit.wrapRat := by
  apply Primrec.fin_curry.mpr
  apply Primrec₂.mk
  exact rat_mul.comp
    (Primrec.ite (Primrec.eq.comp .snd (.const 0)) (.const 1) (.const 10))
    (rat_sub.comp
      (rat_div.comp Primrec.fin_app
        (Primrec.ite (Primrec.eq.comp .snd (.const 0)) (.const 1) (.const 10)))
      (rat_int.comp (rat_floor.comp (rat_div.comp Primrec.fin_app
        (Primrec.ite (Primrec.eq.comp .snd (.const 0)) (.const 1) (.const 10))))))

theorem circuit_jetApprox (e : Fin 3 → Circuit) :
    Primrec (fun p : List (Fin 4) × (Fin 4 → ℚ) × ℕ => Circuit.jetApprox e p.1 p.2.1 p.2.2) := by
  apply Primrec.fin_curry.mpr
  apply Primrec₂.mk
  exact circuit_approx.comp
    ((circuit_mixed.comp (Primrec.fin_app.comp (.const e) .snd) (Primrec.fst.comp .fst)).pair
      ((circuit_wrapRat.comp (Primrec.fst.comp (Primrec.snd.comp .fst))).pair
        (Primrec.snd.comp (Primrec.snd.comp .fst))))

theorem partrec_code {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α →. β} (h : Partrec f) : ∃ c : Nat.Partrec.Code,
      ∀ a b, b ∈ f a → encode b ∈ c.eval (encode a) := by
  obtain ⟨c,hc⟩ := Nat.Partrec.Code.exists_code.mp h
  refine ⟨c,fun a b hb => ?_⟩
  rw [hc]
  simp only [encodek,Part.coe_some,Part.bind_some]
  exact Part.mem_map encode hb

end Computing

theorem HasCircuit.effectiveBounds {u : Field} (h : HasCircuit u) (hu : Smooth u)
    (hx : SpatiallyPeriodic u) (ht : OnePeriodic u) : EffectiveBounds u := by
  obtain ⟨e,he⟩ := h
  obtain ⟨c,hc⟩ := Computing.partrec_code (Computing.circuit_jetBound e).to_comp.partrec
  refine ⟨c,fun a => ⟨Circuit.jetBound e a, hc a _ (Part.mem_some _),
    Circuit.jetBound_nonneg e a, circuit_periodic_bound hu hx ht he a⟩⟩

theorem norm_flatten (z : SpaceTime) : ‖flatten z‖ = ‖z‖ := by
  rw [Prod.norm_def]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (le_trans (norm_nonneg z.1) (le_max_left _ _))).mpr
    intro j
    fin_cases j
    · exact le_max_left _ _
    all_goals exact (norm_le_pi_norm z.2 _).trans (le_max_right _ _)
  · apply max_le
    · exact norm_le_pi_norm (flatten z) 0
    · apply pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.mpr
      intro j
      exact (show ‖z.2 j‖ ≤ ‖flatten z‖ by
        fin_cases j
        · exact norm_le_pi_norm (flatten z) 1
        · exact norm_le_pi_norm (flatten z) 2
        · exact norm_le_pi_norm (flatten z) 3)

theorem spacetime_expansion (z : SpaceTime) :
    z = ∑ j : Fin 4, flatten z j • spacetimeBasis j := by
  apply Prod.ext
  · simp [flatten,spacetimeBasis,Fin.sum_univ_succ]
  · ext k
    fin_cases k <;> simp [flatten,spacetimeBasis,basis,Fin.sum_univ_succ]

def jetLipschitz (B : List (Fin 4) → ℚ) (a : List (Fin 4)) : ℚ :=
  ∑ j : Fin 4, B (j::a)

theorem jetLipschitz_nonneg {B : List (Fin 4) → ℚ} (h : ∀ a, 0 ≤ B a)
    (a : List (Fin 4)) : 0 ≤ jetLipschitz B a := Finset.sum_nonneg (fun _ _ => h _)

theorem mixed_lipschitz {u : Field} (hu : Smooth u) {B : List (Fin 4) → ℚ}
    (hB : ∀ a, 0 ≤ B a) (hb : ∀ a z, ‖mixedDerivative u a z‖ ≤ (B a:ℝ))
    (a : List (Fin 4)) (z w : SpaceTime) :
    ‖mixedDerivative u a z - mixedDerivative u a w‖ ≤ (jetLipschitz B a:ℝ)*‖z-w‖ := by
  have hd (x : SpaceTime) : ‖fderiv ℝ (mixedDerivative u a) x‖ ≤ (jetLipschitz B a:ℝ) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by exact_mod_cast jetLipschitz_nonneg hB a)
    intro v
    have he : fderiv ℝ (mixedDerivative u a) x v =
        ∑ j : Fin 4, flatten v j • mixedDerivative u (j::a) x := by
      conv_lhs => rw [spacetime_expansion v]
      simp only [map_sum,map_smul,mixedDerivative]
    rw [he]
    apply (norm_sum_le _ _).trans
    calc
      ∑ j : Fin 4, ‖flatten v j • mixedDerivative u (j::a) x‖ ≤
          ∑ j : Fin 4, (B (j::a):ℝ) * ‖v‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_smul,mul_comm]
        exact mul_le_mul (hb (j::a) x)
          ((norm_le_pi_norm (flatten v) j).trans_eq (norm_flatten v))
          (norm_nonneg _) (by exact_mod_cast hB (j::a))
      _ = _ := by simp [jetLipschitz,Finset.sum_mul]
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => (mixedDerivative_contDiff hu a).differentiable (by simp) x)
    (fun x _ => hd x) convex_univ (Set.mem_univ w) (Set.mem_univ z)

namespace Computing

theorem jetLipschitz_pr {B : List (Fin 4) → ℚ} (hB : Primrec B) : Primrec (jetLipschitz B) :=
  fin_sum_rat (fun j => hB.comp (Primrec.list_cons.comp (.const j) .id))

end Computing
end Solenoidal

end OAI
