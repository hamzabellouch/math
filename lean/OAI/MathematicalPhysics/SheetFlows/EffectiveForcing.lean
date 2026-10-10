import Mathlib
import OAI.MathematicalPhysics.SheetFlows.FormulaProfiles
import OAI.MathematicalPhysics.SheetFlows.CircuitPrograms

namespace OAI

/-! SheetFlows effective forcing. -/

section
open Set Filter Encodable
open scoped BigOperators Topology
namespace Solenoidal
namespace Computing

def readCode {α : Type*} [Primcodable α] [Inhabited α] (c : Nat.Partrec.Code) (n : ℕ) : Part α :=
  (c.eval n).map (fun k => (decode k).getD default)

theorem readCode_pr {α : Type*} [Primcodable α] [Inhabited α] :
    Partrec₂ (@readCode α _ _) := by
  exact Nat.Partrec.Code.eval_part.map
    ((Primrec.option_getD_default.comp (Primrec.decode.comp .snd)).to_comp.to₂)

theorem readCode_mem {α : Type*} [Primcodable α] [Inhabited α]
    {c : Nat.Partrec.Code} {n : ℕ} {a : α} (h : encode a ∈ c.eval n) : a ∈ readCode c n := by
  unfold readCode
  have hh := Part.mem_map (fun k => (decode k).getD (default:α)) h
  simpa only [encodek,Option.getD_some] using hh

def precision (L ε : ℚ) : Part ℕ :=
  Nat.rfind (fun n => Part.some (decide (L*(1/2:ℚ)^n < ε/2)))

theorem precision_pr : Partrec₂ precision := by
  exact Partrec.rfind
    ((rat_lt.comp (rat_mul.comp (Primrec.fst.comp .fst)
      (rat_pow.comp (.const (1/2)) .snd))
      (rat_div.comp (Primrec.snd.comp .fst) (.const 2))).decide.to_comp.partrec.to₂)

abbrev BallVector := Fin 3 → QBall
abbrev RationalPoint := Fin 4 → ℚ
abbrev JetRequest := List (Fin 4) × RationalPoint × ℕ
abbrev BallOracle := JetRequest →. BallVector

def radiusSum (b : BallVector) : ℚ := ∑ j, (b j).2

def centers (b : BallVector) : Fin 3 → ℚ := fun j => (b j).1

theorem radiusSum_pr : Primrec radiusSum :=
  fin_sum_rat (fun j => Primrec.snd.comp (Primrec.fin_app.comp .id (.const j)))

theorem centers_pr : Primrec centers := by
  apply Primrec.fin_curry.mpr
  exact (Primrec.fst.comp Primrec.fin_app).to₂

def ballTest (ε : ℚ) (b : BallVector) : Bool := decide (radiusSum b < ε/2)

theorem ballTest_pr : Primrec₂ ballTest :=
  (rat_lt.comp (radiusSum_pr.comp .snd) (rat_div.comp .fst (.const 2))).decide.to₂

def improve (A : BallOracle) (p : List (Fin 4) × RationalPoint × ℚ) : Part (Fin 3 → ℚ) :=
  (Nat.rfind (fun n => (A (p.1,p.2.1,n)).map (ballTest p.2.2))).bind fun n =>
    (A (p.1,p.2.1,n)).map centers

theorem improve_pr {A : BallOracle} (hA : Partrec A) : Partrec (improve A) := by
  have ha : Partrec (fun p : (List (Fin 4) × RationalPoint × ℚ) × ℕ =>
      A (p.1.1,p.1.2.1,p.2)) :=
    hA.comp ((Primrec.fst.comp .fst).pair
      ((Primrec.fst.comp (Primrec.snd.comp .fst)).pair .snd)).to_comp
  have hp : Partrec₂ (fun p : List (Fin 4) × RationalPoint × ℚ => fun n =>
      (A (p.1,p.2.1,n)).map (ballTest p.2.2)) :=
    (ha.map (ballTest_pr.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp .fst)))
      .snd).to_comp.to₂).to₂
  exact (Partrec.rfind hp).bind
    (ha.map (centers_pr.comp .snd).to_comp.to₂).to₂

def evalJets (B : List (Fin 4) → ℚ) (A : BallOracle)
    (p : List (Fin 4) × Nat.Partrec.Code × ℚ) : Part (Fin 3 → ℚ) :=
  (precision (jetLipschitz B p.1) p.2.2).bind fun n =>
    (readCode p.2.1 n).bind fun q => improve A (p.1,q,p.2.2)

theorem evalJets_pr {B : List (Fin 4) → ℚ} (hB : Primrec B)
    {A : BallOracle} (hA : Partrec A) : Partrec (evalJets B A) := by
  have hn : Partrec (fun p : List (Fin 4) × Nat.Partrec.Code × ℚ =>
      precision (jetLipschitz B p.1) p.2.2) :=
    precision_pr.comp ((jetLipschitz_pr hB).comp .fst).to_comp (Primrec.snd.comp .snd).to_comp
  have hq : Partrec (fun p : (List (Fin 4) × Nat.Partrec.Code × ℚ) × ℕ =>
      @readCode RationalPoint _ _ p.1.2.1 p.2) :=
    readCode_pr.comp (Primrec.fst.comp (Primrec.snd.comp .fst)).to_comp Primrec.snd.to_comp
  exact hn.bind (hq.bind
    ((improve_pr hA).comp ((Primrec.fst.comp (Primrec.fst.comp .fst)).pair
      (Primrec.snd.pair (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp .fst))))).to_comp).to₂).to₂

end Computing
end Solenoidal
end

section
open Set Filter Encodable
open scoped BigOperators Topology
namespace Solenoidal
namespace Computing

theorem precision_correct (L ε : ℚ) (hε : 0 < ε) :
    ∃ n, n ∈ precision L ε ∧ L*(1/2:ℚ)^n < ε/2 := by
  have hlim : Tendsto (fun n : ℕ => (L:ℝ)*(1/2:ℝ)^n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)).const_mul (L:ℝ)
  have heps : (0:ℝ) < (ε:ℝ)/2 := by exact_mod_cast (div_pos hε (by norm_num : (0:ℚ)<2))
  obtain ⟨n,hn⟩ := (hlim.eventually (gt_mem_nhds heps)).exists
  have hnq : L*(1/2:ℚ)^n < ε/2 := by
    apply (Rat.cast_lt (K := ℝ)).mp
    simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hn
  have hd : (precision L ε).Dom := Nat.rfind_dom.mpr
    ⟨n,by simpa only [Part.mem_some_iff,true_eq_decide_iff] using hnq,
      fun {_} _ => trivial⟩
  obtain ⟨k,hk⟩ := Part.dom_iff_mem.mp hd
  refine ⟨k,hk,?_⟩
  have hh := Nat.rfind_spec hk
  simpa only [Part.mem_some_iff,true_eq_decide_iff] using hh

def OracleCorrect (A : BallOracle) (u : Field) : Prop := ∀ a q,
  ∃ b : ℕ → BallVector, (∀ n, b n ∈ A (a,q,n)) ∧
    ∀ j, QBall.Approximates (fun n => b n j) (mixedDerivative u a (Circuit.ofRational q) j)

theorem radiusSum_nonneg {b : BallVector} {v : Space} (h : ∀ j, (b j).Contains (v j)) :
    0 ≤ radiusSum b := Finset.sum_nonneg (fun j _ => QBall.radius_nonneg (h j))

theorem centers_error {b : BallVector} {v : Space} (h : ∀ j, (b j).Contains (v j)) :
    ‖(fun j => (centers b j:ℝ)) - v‖ ≤ (radiusSum b:ℝ) := by
  apply (pi_norm_le_iff_of_nonneg (by exact_mod_cast radiusSum_nonneg h)).mpr
  intro j
  exact (h j).trans (by exact_mod_cast
    Finset.single_le_sum (fun k _ => QBall.radius_nonneg (h k)) (Finset.mem_univ j))

theorem improve_correct {A : BallOracle} {u : Field} (hA : OracleCorrect A u)
    (a : List (Fin 4)) (q : RationalPoint) (ε : ℚ) (hε : 0 < ε) :
    ∃ r : Fin 3 → ℚ, r ∈ improve A (a,q,ε) ∧
      ‖(fun j => (r j:ℝ)) - mixedDerivative u a (Circuit.ofRational q)‖ < (ε:ℝ)/2 := by
  obtain ⟨b,hb,happrox⟩ := hA a q
  have hlim : Tendsto (fun n => (radiusSum (b n):ℝ)) atTop (𝓝 0) := by
    simpa [radiusSum] using tendsto_finsetSum Finset.univ (fun j _ => (happrox j).radius)
  have heps : (0:ℝ) < (ε:ℝ)/2 := by exact_mod_cast (div_pos hε (by norm_num : (0:ℚ)<2))
  obtain ⟨n,hn⟩ := (hlim.eventually (gt_mem_nhds heps)).exists
  have hnq : radiusSum (b n) < ε/2 := by exact_mod_cast hn
  have htest (m : ℕ) : ballTest ε (b m) ∈ (A (a,q,m)).map (ballTest ε) :=
    Part.mem_map _ (hb m)
  have hd : (Nat.rfind (fun m => (A (a,q,m)).map (ballTest ε))).Dom := by
    apply Nat.rfind_dom.mpr
    refine ⟨n,?_,fun {m} _ => (htest m).1⟩
    simpa only [ballTest,decide_eq_true hnq] using htest n
  obtain ⟨k,hk⟩ := Part.dom_iff_mem.mp hd
  have heq : ballTest ε (b k) = true := Part.mem_unique (htest k) (Nat.rfind_spec hk)
  have he : radiusSum (b k) < ε/2 := of_decide_eq_true heq
  refine ⟨centers (b k),Part.mem_bind hk (Part.mem_map centers (hb k)),?_⟩
  exact (centers_error (fun j => (happrox j).contains k)).trans_lt (by exact_mod_cast he)

theorem ofRational_distance (q : RationalPoint) (z : SpaceTime) :
    ‖Circuit.ofRational q - z‖ = ‖(fun j => (q j:ℝ)) - flatten z‖ := by
  rw [← norm_flatten]
  congr 1
  ext j
  fin_cases j <;> rfl

theorem evalJets_correct {u : Field} (hu : Smooth u) {B : List (Fin 4) → ℚ}
    (hB : ∀ a, 0 ≤ B a) (hb : ∀ a z, ‖mixedDerivative u a z‖ ≤ (B a:ℝ))
    {A : BallOracle} (hA : OracleCorrect A u)
    (a : List (Fin 4)) (c : Nat.Partrec.Code) (z : SpaceTime) (hc : NamesPoint c z)
    (ε : ℚ) (hε : 0 < ε) : ∃ r : Fin 3 → ℚ, r ∈ evalJets B A (a,c,ε) ∧
      ‖(fun j => (r j:ℝ)) - mixedDerivative u a z‖ < (ε:ℝ) := by
  obtain ⟨n,hn,hnlt⟩ := precision_correct (jetLipschitz B a) ε hε
  obtain ⟨q,hq,hqerr⟩ := hc n
  obtain ⟨r,hr,hrerr⟩ := improve_correct hA a q ε hε
  refine ⟨r,Part.mem_bind hn (Part.mem_bind (readCode_mem hq) hr),?_⟩
  have hdist : ‖Circuit.ofRational q-z‖ ≤ (1/2:ℝ)^n := by
    rwa [ofRational_distance]
  have hlip := mixed_lipschitz hu hB hb a (Circuit.ofRational q) z
  have herr : ‖mixedDerivative u a (Circuit.ofRational q) - mixedDerivative u a z‖ < (ε:ℝ)/2 := by
    apply hlip.trans_lt
    apply (mul_le_mul_of_nonneg_left hdist (by exact_mod_cast jetLipschitz_nonneg hB a)).trans_lt
    have hh : ((jetLipschitz B a * (1/2:ℚ)^n : ℚ):ℝ) < ((ε/2:ℚ):ℝ) :=
      Rat.cast_lt.mpr hnlt
    simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hh
  calc
    ‖(fun j => (r j:ℝ)) - mixedDerivative u a z‖ ≤
        ‖(fun j => (r j:ℝ)) - mixedDerivative u a (Circuit.ofRational q)‖ +
        ‖mixedDerivative u a (Circuit.ofRational q) - mixedDerivative u a z‖ := by
          simpa only [dist_eq_norm] using dist_triangle
            (fun j => (r j:ℝ)) (mixedDerivative u a (Circuit.ofRational q))
            (mixedDerivative u a z)
    _ < (ε:ℝ)/2+(ε:ℝ)/2 := add_lt_add hrerr herr
    _ = _ := by ring

end Computing

theorem effective_of_oracle {u : Field} (hu : Smooth u) {B : List (Fin 4) → ℚ}
    (hBpr : Primrec B) (hB : ∀ a, 0 ≤ B a)
    (hb : ∀ a z, ‖mixedDerivative u a z‖ ≤ (B a:ℝ))
    {A : Computing.BallOracle} (hApr : Partrec A) (hA : Computing.OracleCorrect A u) : Effective u := by
  obtain ⟨e,he⟩ := Computing.partrec_code (Computing.evalJets_pr hBpr hApr)
  refine ⟨e,fun a c z hc ε hε => ?_⟩
  obtain ⟨r,hr,herr⟩ := Computing.evalJets_correct hu hB hb hA a c z hc ε hε
  have hh := he (a,c,ε) r hr
  exact ⟨r,hh,herr⟩

theorem HasCircuit.effective {u : Field} (h : HasCircuit u) (hu : Smooth u)
    (hx : SpatiallyPeriodic u) (ht : OnePeriodic u) : Effective u := by
  obtain ⟨e,he⟩ := h
  apply effective_of_oracle hu (Computing.circuit_jetBound e) (Circuit.jetBound_nonneg e)
    (circuit_periodic_bound hu hx ht he) (Computing.circuit_jetApprox e).to_comp.partrec
  intro a q
  exact ⟨Circuit.jetApprox e a q,fun precision => Part.mem_some (Circuit.jetApprox e a q precision),
    circuit_periodic_approx hu hx ht he a q⟩

end Solenoidal
end

open Set Filter Encodable
open scoped BigOperators Topology
namespace Solenoidal

theorem mixedDerivative_add {u v : Field} (hu : Smooth u) (hv : Smooth v) (a : List (Fin 4)) :
    mixedDerivative (u+v) a = mixedDerivative u a + mixedDerivative v a := by
  induction a with
  | nil => rfl
  | cons j a ih =>
    funext z
    rw [mixedDerivative,ih]
    dsimp only
    rw [fderiv_add ((mixedDerivative_contDiff hu a).differentiable (by simp) z)
      ((mixedDerivative_contDiff hv a).differentiable (by simp) z)]
    rfl

theorem mixedDerivative_smul {u : Field} (hu : Smooth u) (r : ℝ) (a : List (Fin 4)) :
    mixedDerivative (r • u) a = r • mixedDerivative u a := by
  induction a with
  | nil => rfl
  | cons j a ih =>
    funext z
    rw [mixedDerivative,ih]
    dsimp only
    rw [fderiv_const_smul ((mixedDerivative_contDiff hu a).differentiable (by simp) z)]
    rfl

theorem smooth_linear {u v : Field} (hu : Smooth u) (hv : Smooth v) (r : ℝ) :
    Smooth (u+r•v) := hu.add (hv.const_smul r)

theorem mixedDerivative_linear {u v : Field} (hu : Smooth u) (hv : Smooth v)
    (r : ℝ) (a : List (Fin 4)) :
    mixedDerivative (u+r•v) a = mixedDerivative u a + r • mixedDerivative v a := by
  rw [mixedDerivative_add (v := r • v) hu (hv.const_smul r),mixedDerivative_smul hv]

namespace Computing

def realBall (c : Nat.Partrec.Code) (n : ℕ) : Part QBall :=
  (@readCode ℚ _ _ c n).map (fun q => (q,(1/2:ℚ)^n))

theorem realBall_pr : Partrec₂ realBall :=
  (readCode_pr.map (Primrec.snd.pair
    (rat_pow.comp (.const (1/2)) (Primrec.snd.comp .fst))).to_comp.to₂)

theorem realBall_correct {c : Nat.Partrec.Code} {r : ℝ} (h : NamesReal c r) :
    ∃ b : ℕ → QBall, (∀ n, b n ∈ realBall c n) ∧ QBall.Approximates b r := by
  classical
  choose q hq he using h
  refine ⟨fun n => (q n,(1/2:ℚ)^n),fun n => Part.mem_map _ (readCode_mem (hq n)),?_,?_⟩
  · intro n
    simpa [QBall.Contains] using he n
  · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1))

def linearBalls (r : QBall) (a b : BallVector) : BallVector := fun j => (a j).add (r.mul (b j))

theorem linearBalls_pr : Primrec (fun p : QBall × BallVector × BallVector => linearBalls p.1 p.2.1 p.2.2) := by
  apply Primrec.fin_curry.mpr
  apply Primrec₂.mk
  exact ball_add.comp
    (Primrec.fin_app.comp (Primrec.fst.comp (Primrec.snd.comp .fst)) .snd)
    (ball_mul.comp (Primrec.fst.comp .fst)
      (Primrec.fin_app.comp (Primrec.snd.comp (Primrec.snd.comp .fst)) .snd))

def linearOracle (c : Nat.Partrec.Code) (A B : BallOracle) (p : JetRequest) : Part BallVector :=
  (realBall c p.2.2).bind fun r => (A p).bind fun a =>
    (B p).map (linearBalls r a)

theorem linearOracle_pr (c : Nat.Partrec.Code) {A B : BallOracle}
    (hA : Partrec A) (hB : Partrec B) : Partrec (linearOracle c A B) := by
  have hr : Partrec (fun p : JetRequest => realBall c p.2.2) :=
    realBall_pr.comp (.const c) (Primrec.snd.comp .snd).to_comp
  have ha : Partrec (fun p : JetRequest × QBall => A p.1) := hA.comp .fst
  have hb : Partrec (fun p : (JetRequest × QBall) × BallVector => B p.1.1) :=
    hB.comp (Primrec.fst.comp .fst).to_comp
  exact hr.bind (ha.bind (hb.map
    (linearBalls_pr.comp ((Primrec.snd.comp (Primrec.fst.comp .fst)).pair
      ((Primrec.snd.comp .fst).pair .snd))).to_comp.to₂).to₂).to₂

theorem linearOracle_correct {c : Nat.Partrec.Code} {r : ℝ} (hc : NamesReal c r)
    {u v : Field} (hu : Smooth u) (hv : Smooth v) {A B : BallOracle}
    (hA : OracleCorrect A u) (hB : OracleCorrect B v) :
    OracleCorrect (linearOracle c A B) (u+r•v) := by
  obtain ⟨br,hbr,hbrc⟩ := realBall_correct hc
  intro a q
  obtain ⟨bu,hbu,hbuc⟩ := hA a q
  obtain ⟨bv,hbv,hbvc⟩ := hB a q
  refine ⟨fun n => linearBalls (br n) (bu n) (bv n),fun n =>
    Part.mem_bind (hbr n) (Part.mem_bind (hbu n) (Part.mem_map _ (hbv n))),?_⟩
  intro j
  rw [mixedDerivative_linear hu hv]
  exact (hbuc j).add (hbrc.mul (hbvc j))

end Computing

theorem NamesReal.rationalBound {c : Nat.Partrec.Code} {r : ℝ} (h : NamesReal c r) :
    ∃ M : ℚ, 0 ≤ M ∧ |r| ≤ (M:ℝ) := by
  obtain ⟨q,hq,he⟩ := h 0
  refine ⟨|q|+1,by positivity,?_⟩
  have hh := abs_sub_comm (q:ℝ) r
  have ht : |r| ≤ |r-(q:ℝ)|+|(q:ℝ)| := by
    simpa using abs_add_le (r-(q:ℝ)) (q:ℝ)
  simp only [pow_zero] at he
  push_cast
  rw [← hh] at ht
  linarith

def linearBound (M : ℚ) (B C : List (Fin 4) → ℚ) (a : List (Fin 4)) : ℚ := B a + M * C a

theorem linearBound_pr (M : ℚ) {B C : List (Fin 4) → ℚ} (hb : Primrec B) (hc : Primrec C) :
    Primrec (linearBound M B C) := Computing.rat_add.comp hb (Computing.rat_mul.comp (.const M) hc)

theorem linearBound_nonneg {M : ℚ} (hM : 0 ≤ M) {B C : List (Fin 4) → ℚ}
    (hb : ∀ a, 0 ≤ B a) (hc : ∀ a, 0 ≤ C a) (a : List (Fin 4)) :
    0 ≤ linearBound M B C a := add_nonneg (hb a) (mul_nonneg hM (hc a))

theorem linearBound_correct {u v : Field} (hu : Smooth u) (hv : Smooth v) {r : ℝ}
    {M : ℚ} (hM : |r| ≤ (M:ℝ)) {B C : List (Fin 4) → ℚ}
    (hb : ∀ a z, ‖mixedDerivative u a z‖ ≤ (B a:ℝ))
    (hc : ∀ a z, ‖mixedDerivative v a z‖ ≤ (C a:ℝ)) (a : List (Fin 4)) (z : SpaceTime) :
    ‖mixedDerivative (u+r•v) a z‖ ≤ (linearBound M B C a:ℝ) := by
  rw [mixedDerivative_linear hu hv]
  apply (norm_add_le _ _).trans
  simp only [Pi.smul_apply,norm_smul,Real.norm_eq_abs,linearBound,Rat.cast_add,Rat.cast_mul]
  exact add_le_add (hb a z) (mul_le_mul hM (hc a z) (norm_nonneg _)
    ((abs_nonneg r).trans hM))

theorem effectiveBounds_of_bound {u : Field} {B : List (Fin 4) → ℚ}
    (hpr : Primrec B) (hn : ∀ a, 0 ≤ B a) (hb : ∀ a z, ‖mixedDerivative u a z‖ ≤ (B a:ℝ)) :
    EffectiveBounds u := by
  obtain ⟨c,hc⟩ := Computing.partrec_code hpr.to_comp.partrec
  exact ⟨c,fun a => ⟨B a,hc a (B a) (Part.mem_some _),hn a,hb a⟩⟩

theorem HasCircuit.computable_linear {u v : Field} (hU : HasCircuit u) (hV : HasCircuit v)
    (hu : Smooth u) (hv : Smooth v) (hux : SpatiallyPeriodic u) (hvx : SpatiallyPeriodic v)
    (hut : OnePeriodic u) (hvt : OnePeriodic v) {r : ℝ} (hr : ComputableReal r) :
    Effective (u+r•v) ∧ EffectiveBounds (u+r•v) := by
  obtain ⟨c,hc⟩ := hr
  obtain ⟨M,hM,hMr⟩ := hc.rationalBound
  obtain ⟨e,he⟩ := hU
  obtain ⟨f,hf⟩ := hV
  let B := linearBound M (Circuit.jetBound e) (Circuit.jetBound f)
  have hBp : Primrec B := linearBound_pr M (Computing.circuit_jetBound e) (Computing.circuit_jetBound f)
  have hBn : ∀ a, 0 ≤ B a := linearBound_nonneg hM (Circuit.jetBound_nonneg e) (Circuit.jetBound_nonneg f)
  have hBb : ∀ a z, ‖mixedDerivative (u+r•v) a z‖ ≤ (B a:ℝ) :=
    linearBound_correct hu hv hMr (circuit_periodic_bound hu hux hut he) (circuit_periodic_bound hv hvx hvt hf)
  constructor
  · apply effective_of_oracle (smooth_linear hu hv r) hBp hBn hBb
      (Computing.linearOracle_pr c (Computing.circuit_jetApprox e).to_comp.partrec
        (Computing.circuit_jetApprox f).to_comp.partrec)
    apply Computing.linearOracle_correct hc hu hv
    · intro a q
      exact ⟨Circuit.jetApprox e a q,fun _ => Part.mem_some _,circuit_periodic_approx hu hux hut he a q⟩
    · intro a q
      exact ⟨Circuit.jetApprox f a q,fun _ => Part.mem_some _,circuit_periodic_approx hv hvx hvt hf a q⟩
  · exact effectiveBounds_of_bound hBp hBn hBb

theorem HasRationalFormula.directForce_effective {u : Field} (h : HasRationalFormula u)
    (hu : Smooth u) (hx : SpatiallyPeriodic u) (ht : OnePeriodic u) {ν : ℝ}
    (hν : ComputableReal ν) : Effective (globalDirectForce ν u) ∧ EffectiveBounds (globalDirectForce ν u) := by
  have hux : SpatiallyPeriodic (Solenoidal.fullTimePartial u) := by
    rw [fullTimePartial_eq_fieldDirectional hu]
    exact fieldDirectional_spatially_periodic hu hx _
  have hut : OnePeriodic (Solenoidal.fullTimePartial u) := by
    rw [fullTimePartial_eq_fieldDirectional hu]
    exact fieldDirectional_onePeriodic hu ht _
  have hvx : SpatiallyPeriodic ((-1:ℝ) • Solenoidal.laplacian u) := by
    intro t x k
    change (-1:ℝ) • (∑ j, Solenoidal.spatialPartial (Solenoidal.spatialPartial u j) j t (x+deck k)) =
      (-1:ℝ) • (∑ j, Solenoidal.spatialPartial (Solenoidal.spatialPartial u j) j t x)
    congr 1
    exact Finset.sum_congr rfl (fun j _ => spatialPartial_spatially_periodic
      (smooth_spatialPartial hu j) (spatialPartial_spatially_periodic hu hx j) j t x k)
  have hvt : OnePeriodic ((-1:ℝ) • Solenoidal.laplacian u) := by
    intro t x
    change (-1:ℝ) • (∑ j, Solenoidal.spatialPartial (Solenoidal.spatialPartial u j) j (t+1) x) =
      (-1:ℝ) • (∑ j, Solenoidal.spatialPartial (Solenoidal.spatialPartial u j) j t x)
    congr 1
    exact Finset.sum_congr rfl (fun j _ => spatialPartial_onePeriodic
      (smooth_spatialPartial hu j) (spatialPartial_onePeriodic hu ht j) j t x)
  have hV : HasCircuit ((-1:ℝ) • Solenoidal.laplacian u) := by
    simpa only [Rat.cast_neg, Rat.cast_one] using (((h.laplacian hu).smul (-1)).circuit)
  have hvs : Smooth ((-1:ℝ) • Solenoidal.laplacian u) :=
    (smooth_laplacian hu).const_smul (-1:ℝ)
  have hh := ((h.fullTimePartial hu).circuit).computable_linear
    hV (smooth_fullTimePartial hu) hvs hux hvx hut hvt hν
  have he : globalDirectForce ν u = Solenoidal.fullTimePartial u + ν • ((-1:ℝ) • Solenoidal.laplacian u) := by
    ext t x j
    simp [globalDirectForce,sub_eq_add_neg]
  rwa [← he] at hh

end Solenoidal

end OAI
