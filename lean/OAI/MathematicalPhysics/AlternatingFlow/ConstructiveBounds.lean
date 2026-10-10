import OAI.MathematicalPhysics.AlternatingFlow.DecoderNames
import OAI.MathematicalPhysics.AlternatingFlow.RecursiveBounds

namespace OAI

section ConstructiveBoundsDevelopment

open scoped BigOperators Topology ContDiff
open Filter

namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding

variable {A : Type*} [Primcodable A]

lemma Scaled.nat {s : A → ℕ → ℝ} (hs : ∀ a n, 0 ≤ s a n)
    (c : A → ℕ) (hc : Computable c) : Scaled s (fun a _ (_ : ℝ) => (c a : ℝ)) :=
  Scaled.const hs _ c hc (by intro a n; simp)

lemma Scaled.cmul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : A → ℕ → ℝ} (hs : ∀ a n, 0 ≤ s a n) {f : A → ℕ → E → ℝ}
    (hf : Scaled s f) (c : ℝ) (B : ℕ) (hc : |c| ≤ B) :
    Scaled s (fun a n x => c * f a n x) :=
  hf.smul hs (fun _ _ => c) (fun _ => B) (Computable.const B) (fun _ _ => hc)

lemma Scaled.affine {s : A → ℕ → ℝ} (hs : ∀ a n, 0 ≤ s a n)
    {f : A → ℝ → ℝ} (hf : Scaled (fun _ _ => 1) (fun a _ => f a))
    (c d : A → ℕ → ℝ) (B : A → ℕ) (hB : Computable B)
    (hc : ∀ a n, |c a n| ≤ (B a : ℝ) * s a n) :
    Scaled s (fun a n x => f a (c a n * x + d a n)) := by
  obtain ⟨sf,C,hC,hfC⟩ := hf
  refine ⟨fun a n => (sf a 0).comp (contDiff_const.mul contDiff_id |>.add contDiff_const),
    fun z => C z * B z.1 ^ z.2,
    Primrec.nat_mul.to_comp.comp hC (nat_pow.to_comp.comp (hB.comp Computable.fst) Computable.snd),
    fun a r n x => ?_⟩
  change ‖iteratedFDeriv ℝ r ((fun y => f a (y + d a n)) ∘
    (c a n • ContinuousLinearMap.id ℝ ℝ)) x‖ ≤ _
  apply (Bounds.norm_comp_linear _ ((sf a 0).comp (contDiff_id.add contDiff_const)) _ r x).trans
  change ‖iteratedFDeriv ℝ r (fun y => f a (y + d a n)) (c a n * x)‖ *
    ‖c a n • ContinuousLinearMap.id ℝ ℝ‖ ^ r ≤ _
  rw [iteratedFDeriv_comp_add_right]
  simp only [norm_smul, Real.norm_eq_abs, ContinuousLinearMap.norm_id, mul_one]
  push_cast
  calc
    _ ≤ (C (a,r) : ℝ) * ((B a : ℝ) * s a n) ^ r := by
      rw [mul_comm, mul_comm (C (a,r) : ℝ)]
      exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hc a n) r)
        (by simpa using hfC a r 0 (c a n * x + d a n)) (norm_nonneg _)
        (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) (hs a n)) r)
    _ = _ := by ring

lemma transition_scaled : Scaled (fun _ : Unit => fun _ => 1)
    (fun _ _ => Real.smoothTransition) :=
  ⟨fun _ _ => Real.smoothTransition.contDiff, fun z => Quantitative.transitionBound z.2,
    transitionBound.to_comp.comp Computable.snd, by intro _ r n x; simpa using Quantitative.transition_jet_bound r x⟩

lemma selector_scaled (b a : A → ℕ) (hB : Computable b) :
    Scaled (fun _ _ => 1) (fun p _ => Profiles.selector (b p) (a p)) := by
  have hT := transition_scaled.param (fun _ : A => ()) (Computable.const ())
  have h₁ := hT.affine (fun _ _ => zero_le_one) (fun p _ => 8 * (b p : ℝ))
    (fun p _ => 2 - 16 * (a p : ℝ)) (fun p => 8 * b p)
    (Primrec.nat_mul.to_comp.comp (Computable.const 8) hB) (by intro p n; simp)
  have h₂ := hT.affine (fun _ _ => zero_le_one) (fun p _ => -(8 * (b p : ℝ)))
    (fun p _ => 16 * (a p : ℝ) + 10) (fun p => 8 * b p)
    (Primrec.nat_mul.to_comp.comp (Computable.const 8) hB) (by intro p n; simp)
  exact (h₁.mul (fun _ _ => zero_le_one) h₂).congr (by intros; dsimp [Profiles.selector]; congr 2 <;> ring)

lemma decoder_scaled : Scaled (fun _ : Machine => fun _ => 1)
    (fun M _ => Profiles.decoder M.base) := by
  refine ⟨fun M _ => Profiles.decoder_smooth M.base (by have := M.base_ge_four; omega),
    fun z => Quantitative.decoderBound z.1.base z.2,
    decoderBound.to_comp.comp (base.to_comp.comp Computable.fst) Computable.snd, ?_⟩
  intro M r n x
  simp only [one_pow, mul_one]
  exact Quantitative.decoder_jet_bound M.base (by have := M.base_ge_four; omega) r x

lemma read_scaled (M : A → Machine) (N : A → ℕ) (hM : Computable M)
    (k : A → ℕ → ℕ) (hk : ∀ a n, k a n ≤ Scales.s (N a) n + 1 + Scales.K (N a) n) :
    Scaled (fun a => Bounds.readScale (M a) (N a))
      (fun a n D => Profiles.decoder (M a).base (((M a).base : ℝ) ^ k a n * D)) := by
  apply (decoder_scaled.param M hM).comp_scaled_linear (fun a => Bounds.readScale_nonneg _ _)
    (fun a n => ((M a).base : ℝ) ^ k a n • ContinuousLinearMap.id ℝ ℝ)
  intro a n
  have hb : (1 : ℝ) ≤ (M a).base := by have := (M a).base_ge_four; exact_mod_cast (by omega : 1 ≤ (M a).base)
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (le_trans zero_le_one hb) _),
    ContinuousLinearMap.norm_id, mul_one, Bounds.readScale] using pow_le_pow_right₀ hb (hk a n)

lemma readC_scaled (M : A → Machine) (N : A → ℕ) (hM : Computable M) :
    Scaled (fun a => Bounds.readScale (M a) (N a)) (fun a => LocalRule.readC (M a) (N a)) :=
  read_scaled M N hM (fun a => Scales.s (N a)) (by intros; omega)

lemma readB_scaled (M : A → Machine) (N : A → ℕ) (hM : Computable M) :
    Scaled (fun a => Bounds.readScale (M a) (N a)) (fun a => LocalRule.readB (M a) (N a)) :=
  read_scaled M N hM _ (by intros; rfl)

lemma readA_scaled (M : A → Machine) (N : A → ℕ) (hM : Computable M) :
    Scaled (fun a => Bounds.readScale (M a) (N a)) (fun a => LocalRule.readA (M a) (N a)) :=
  (read_scaled M N hM (fun a n => Scales.s (N a) n + 1) (by intros; omega)).sub
    ((readB_scaled M N hM).smul (fun a => Bounds.readScale_nonneg _ _) _
      (fun _ => 1) (Computable.const 1) (fun a n => by simpa using Bounds.inverse_power_bound (M a) (Scales.K (N a) n)))

lemma updates_scaled (M : A → Machine) (N a l : A → ℕ) (r : A → Rule)
    (hM : Computable M) (ha : Computable a) (hl : Computable l) (hr : Computable r) :
    Scaled (fun p => Bounds.readScale (M p) (N p))
      (fun p n D => LocalRule.updateLeft (M p).base (a p) (l p) (r p)
        (LocalRule.readA (M p) (N p) n D) (LocalRule.readB (M p) (N p) n D)) ∧
    Scaled (fun p => Bounds.readScale (M p) (N p))
      (fun p n D => LocalRule.updateRight (M p).base (a p) (l p) (r p)
        (LocalRule.readA (M p) (N p) n D) (LocalRule.readB (M p) (N p) n D)) := by
  let s := fun p => Bounds.readScale (M p) (N p)
  have hs : ∀ p n, 0 ≤ s p n := fun p => Bounds.readScale_nonneg _ _
  have hhA := readA_scaled M N hM
  have hhB := readB_scaled M N hM
  have cb := base.to_comp.comp hM
  have hrw := Computable.fst.comp (Computable.snd.comp hr)
  have hb (p : A) (n : ℕ) : |((M p).base : ℝ)| ≤ ((M p).base : ℝ) := by simp
  have hdiv {f : A → ℕ → ℝ → ℝ} (hf : Scaled s f) :
      Scaled s (fun p n D => f p n D / (M p).base) := by
    have h := hf.smul hs (fun p _ => ((M p).base : ℝ)⁻¹) (fun _ => 1) (Computable.const 1)
      (fun p _ => by simpa using Bounds.inverse_power_bound (M p) 1)
    exact h.congr (by intros; simp [div_eq_mul_inv, mul_comm])
  have h2l := Scaled.nat hs (fun p => 2 * l p) (Primrec.nat_mul.to_comp.comp (Computable.const 2) hl)
  have h2a := Scaled.nat hs (fun p => 2 * a p) (Primrec.nat_mul.to_comp.comp (Computable.const 2) ha)
  have h2w := Scaled.nat hs (fun p => 2 * (r p).2.1) (Primrec.nat_mul.to_comp.comp (Computable.const 2) hrw)
  have hLeft := ((hhA.smul hs (fun p _ => ((M p).base : ℝ)) (fun p => (M p).base) cb hb).sub h2l).ite hs
    (hhA.ite hs (hdiv (h2w.add hhA)) (fun p _ => (r p).2.2 = 1)) (fun p _ => (r p).2.2 = 0)
  have hR := (hhB.smul hs (fun p _ => ((M p).base : ℝ)) (fun p => (M p).base) cb hb).sub h2a
  have hRight := (hdiv (h2l.add (hdiv (h2w.add hR)))).ite hs
    ((hdiv (h2w.add hR)).ite hs hR (fun p _ => (r p).2.2 = 1)) (fun p _ => (r p).2.2 = 0)
  constructor
  · exact hLeft.congr (by intro p n x; dsimp [LocalRule.updateLeft]; push_cast; split_ifs <;> rfl)
  · exact hRight.congr (by intro p n x; dsimp [LocalRule.updateRight]; push_cast; split_ifs <;> rfl)

lemma branchNumerator_scaled (M : A → Machine) (N a l : A → ℕ) (r : A → Rule)
    (hM : Computable M) (ha : Computable a) (hl : Computable l) (hr : Computable r) :
    Scaled (fun p => Bounds.readScale (M p) (N p))
      (fun p n D => LocalRule.branchNumerator (M p).base (Scales.K (N p) (n+1)) (a p) (l p) (r p)
        (LocalRule.readA (M p) (N p) n D) (LocalRule.readB (M p) (N p) n D)) := by
  have hs := fun p => Bounds.readScale_nonneg (M p) (N p)
  obtain ⟨hl',hr'⟩ := updates_scaled M N a l r hM ha hl hr
  exact ((Scaled.nat hs (fun p => 2 * (r p).1)
    (Primrec.nat_mul.to_comp.comp (Computable.const 2) (Computable.fst.comp hr))).add hl').add
    (hr'.smul hs (fun p n => (((M p).base : ℝ) ^ Scales.K (N p) (n+1))⁻¹)
      (fun _ => 1) (Computable.const 1) (fun p n => by simpa using Bounds.inverse_power_bound (M p) (Scales.K (N p) (n+1))))

attribute [local irreducible] LocalRule.readA LocalRule.readB LocalRule.readC
  Profiles.selector LocalRule.branchNumerator

lemma branch_scaled (M : A → Machine) (N q a : A → ℕ)
    (hM : Computable M) (hq : Computable q) (ha : Computable a) :
    Scaled (fun p => Bounds.readScale (M p) (N p))
      (fun p n D => LocalRule.branch (M p) (N p) n (q p) (a p)
        (LocalRule.readA (M p) (N p) n D) (LocalRule.readB (M p) (N p) n D)) := by
  have hs := fun p => Bounds.readScale_nonneg (M p) (N p)
  let r := fun p => (M p).command (q p) (a p)
  have hr : Computable r := command.to_comp.comp (hM.pair (hq.pair ha))
  have hb := base.to_comp.comp hM
  have hread := (readA_scaled M N hM).param
    (Prod.fst : A × ℕ → A) Computable.fst
  have hout : Scaled (fun _ : A × ℕ => fun _ => (1:ℝ)) (fun p _ => Profiles.selector (M p.1).base p.2) := selector_scaled (fun p : A × ℕ => (M p.1).base) Prod.snd (hb.comp Computable.fst)
  have hsel : Scaled (fun p : A × ℕ => Bounds.readScale (M p.1) (N p.1))
      (fun p n => Profiles.selector (M p.1).base p.2 ∘ LocalRule.readA (M p.1) (N p.1) n) :=
    Scaled.comp (A := A × ℕ) (E := ℝ) (F := ℝ) (G := ℝ)
      (s := fun p => Bounds.readScale (M p.1) (N p.1))
      (f := fun p => LocalRule.readA (M p.1) (N p.1))
      (g := fun p => Profiles.selector (M p.1).base p.2) (fun p => hs p.1) hread hout
  have hnum := branchNumerator_scaled (fun p : A × ℕ => M p.1) (fun p => N p.1)
    (fun p => a p.1) Prod.snd (fun p => r p.1) (hM.comp Computable.fst)
    (ha.comp Computable.fst) Computable.snd (hr.comp Computable.fst)
  let S := fun (p : A × ℕ) n => Profiles.selector (M p.1).base p.2 ∘ LocalRule.readA (M p.1) (N p.1) n
  let V := fun (p : A × ℕ) n D => LocalRule.branchNumerator (M p.1).base (Scales.K (N p.1) (n+1)) (a p.1) p.2 (r p.1)
    (LocalRule.readA (M p.1) (N p.1) n D) (LocalRule.readB (M p.1) (N p.1) n D)
  have hprod : Scaled (fun p : A × ℕ => Bounds.readScale (M p.1) (N p.1)) (fun p n D => S p n D * V p n D) :=
    Scaled.mul (A := A × ℕ) (E := ℝ) (s := fun p => Bounds.readScale (M p.1) (N p.1)) (f := S) (g := V) (fun p => hs p.1) hsel hnum
  have hsum := hprod.sum_range hs
    (fun p => (M p).alphabet) (alphabet.to_comp.comp hM)
  exact (hsum.ite hs (branchNumerator_scaled M N a (fun _ => 0) r hM ha (Computable.const 0) hr)
    (fun p _ => (r p).2.2 = 0)).congr (by intros; simp only [LocalRule.branch, S, V, r, Function.comp_apply, ite_apply])

attribute [local irreducible] LocalRule.branch

lemma writeCore_scaled : Scaled (fun p : Machine × ℕ => Bounds.readScale p.1 p.2)
    (fun p => Bounds.writeCore p.1 p.2) := by
  let A := ((Machine × ℕ) × ℕ) × ℕ
  let M := fun p : A => p.1.1.1
  let N := fun p : A => p.1.1.2
  let q := fun p : A => p.1.2
  let a := fun p : A => p.2
  have hM : Computable M := Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hq : Computable q := Computable.snd.comp Computable.fst
  have ha : Computable a := Computable.snd
  have hs := fun p => Bounds.readScale_nonneg (M p) (N p)
  have hC := (readC_scaled M N hM).comp (A := A) (E := ℝ) (F := ℝ) (G := ℝ) (s := fun p => Bounds.readScale (M p) (N p)) (g := fun p => Profiles.selector (M p).base (q p)) hs (selector_scaled (fun p => (M p).base) q (base.to_comp.comp hM))
  have hB := (readB_scaled M N hM).comp (A := A) (E := ℝ) (F := ℝ) (G := ℝ) (s := fun p => Bounds.readScale (M p) (N p)) (g := fun p => Profiles.selector (M p).base (a p)) hs (selector_scaled (fun p => (M p).base) a (base.to_comp.comp hM))
  have hsum := ((hC.mul (E := ℝ) hs hB).mul (E := ℝ) hs (branch_scaled M N q a hM hq ha)).sum_range
    (fun p : (Machine × ℕ) × ℕ => Bounds.readScale_nonneg p.1.1 p.1.2)
    (fun p => p.1.1.alphabet) (alphabet.to_comp.comp (Computable.fst.comp Computable.fst))
  have hsum' := hsum.sum_range (fun p : Machine × ℕ => Bounds.readScale_nonneg p.1 p.2)
    (fun p => p.1.states + 1) (Computable.succ.comp (states.to_comp.comp Computable.fst))
  exact (hsum'.smul (A := Machine × ℕ) (E := ℝ) (F := ℝ) (fun p => Bounds.readScale_nonneg p.1 p.2) (fun p _ => 1 / (p.1.base : ℝ))
    (fun _ => 1) (Computable.const 1) (fun p _ => by simpa using Bounds.inverse_power_bound p.1 1)).congr
    (by intros; rfl)

lemma haltWeight_scaled : Scaled (fun p : Machine × ℕ => Bounds.readScale p.1 p.2)
    (fun p => LocalRule.haltWeight p.1 p.2) := by
  have hs := fun p : (Machine × ℕ) × ℕ => Bounds.readScale_nonneg p.1.1 p.1.2
  have h := (readC_scaled (fun p : (Machine × ℕ) × ℕ => p.1.1) (fun p => p.1.2)
    (Computable.fst.comp Computable.fst)).comp (A := (Machine × ℕ) × ℕ) (s := fun p => Bounds.readScale p.1.1 p.1.2) (E := ℝ) (F := ℝ) (G := ℝ) (g := fun p : (Machine × ℕ) × ℕ => Profiles.selector p.1.1.base p.2) hs
    (selector_scaled (fun p : (Machine × ℕ) × ℕ => p.1.1.base) Prod.snd (base.to_comp.comp (Computable.fst.comp Computable.fst)))
  have hzero : Scaled (fun p : (Machine × ℕ) × ℕ => Bounds.readScale p.1.1 p.1.2)
      (fun _ _ (_ : ℝ) => (0 : ℝ)) := Scaled.const hs _ (fun _ => 0) (Computable.const 0) (by intros; simp)
  have hi := (h.ite (A := (Machine × ℕ) × ℕ) (E := ℝ) (F := ℝ) hs hzero (fun p _ => p.2 = p.1.1.states ∨ p.2 ∈ p.1.1.haltingStates)).sum_range (A := Machine × ℕ) (E := ℝ) (F := ℝ)
    (fun p => Bounds.readScale_nonneg p.1 p.2) (fun p => p.1.states + 1)
    (Computable.succ.comp (states.to_comp.comp Computable.fst))

  exact hi.congr (by intros; simp only [LocalRule.haltWeight, Function.comp_apply, ite_apply])

lemma Scaled.coord {s : A → ℕ → ℝ} (hs : ∀ a n, 0 ≤ s a n)
    {f : A → ℕ → ℝ → ℝ} (hf : Scaled s f) (idx : A → ℕ → Fin 3) :
    Scaled s (fun a n (x : Space) => f a n (x (idx a n))) := by
  apply hf.comp_linear (E := ℝ) (F := ℝ) (G := Space) hs
    (fun a n => PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) (idx a n))
    (fun _ => 1) (Computable.const 1)
  intro a n
  simp only [Nat.cast_one]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul, PiLp.proj_apply] using PiLp.norm_apply_le x (idx a n)

lemma cutoff_scaled : Scaled (fun _ : Unit => fun _ => 1) (fun _ _ => Spatial.cutoff) := by
  have h₁ := transition_scaled.affine (fun _ _ => zero_le_one)
    (fun _ _ => -1) (fun _ _ => 3) (fun _ => 1) (Computable.const 1) (by intros; norm_num)
  have h₂ := transition_scaled.affine (fun _ _ => zero_le_one)
    (fun _ _ => 1) (fun _ _ => 3) (fun _ => 1) (Computable.const 1) (by intros; norm_num)
  have h := h₁.mul (E := ℝ) (fun _ _ => zero_le_one) h₂
  have hi (i : Fin 3) := h.coord (fun _ _ => zero_le_one) (fun _ _ => i)
  exact (((hi 0).mul (E := Space) (fun _ _ => zero_le_one) (hi 1)).mul
    (E := Space) (fun _ _ => zero_le_one) (hi 2)).congr
    (by intro p n x; simp [Spatial.cutoff, Fin.prod_univ_succ, mul_assoc, sub_eq_add_neg,
      add_comm])

lemma coord_jet_on_box (i : Fin 3) (r : ℕ) (x : Space) (hx : x ∈ Spatial.box) :
    ‖iteratedFDeriv ℝ r (fun x : Space => x i) x‖ ≤ 3 := by
  cases r with
  | zero => simpa using hx i
  | succ r =>
    let L := PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i
    have hd : fderiv ℝ (fun x : Space => x i) = fun _ => L := by
      funext x; exact (Spatial.coord_hasFDeriv i x).fderiv
    rw [← norm_iteratedFDeriv_fderiv, hd]
    cases r with
    | zero =>
      simp only [norm_iteratedFDeriv_zero]
      have hL : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one
        (fun y => by simpa only [L, PiLp.proj_apply, one_mul] using PiLp.norm_apply_le y i)
      linarith
    | succ r => rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero _), Pi.zero_apply, norm_zero]; norm_num

lemma cutoff_coordinate_scaled (idx : A → ℕ → Fin 3) :
    Scaled (fun _ _ => 1) (fun a n (x : Space) => Spatial.cutoff x * x (idx a n)) := by
  obtain ⟨_,B,hB,hcut⟩ := cutoff_scaled
  have hc : Computable (fun r => B ((),r)) := hB.comp ((Computable.const ()).pair Computable.id)
  let C := fun r => ∑ i ∈ Finset.range (r+1), r.choose i * B ((),i) * 3
  have hi : Computable₂ (fun r i : ℕ => r.choose i * B ((),i) * 3) :=
    Primrec.nat_mul.to_comp.comp (Primrec.nat_mul.to_comp.comp
      (choose.to_comp.comp Computable.fst Computable.snd) (hc.comp Computable.snd)) (Computable.const 3)
  have hC : Computable C := (nat_sum_range hi).comp Computable.id Computable.succ
  refine ⟨fun a n => Spatial.cutoff_smooth.mul (Spatial.coord_smooth (idx a n)),
    fun z => C z.2, hC.comp Computable.snd, fun a r n x => ?_⟩
  simp only [one_pow, mul_one]
  by_cases hx : x ∈ Spatial.box
  · apply (norm_iteratedFDeriv_mul_le Spatial.cutoff_smooth (Spatial.coord_smooth (idx a n)) x
      (WithTop.coe_le_coe.mpr le_top : (r : ℕ∞ω) ≤ ∞)).trans
    simp only [C, Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul (mul_le_mul_of_nonneg_left (by simpa using hcut () i 0 x) (Nat.cast_nonneg _))
      (coord_jet_on_box _ _ _ hx) (norm_nonneg _) (by positivity)
  · have hn : x ∉ tsupport (fun x : Space => Spatial.cutoff x * x (idx a n)) :=
      fun h => hx (Spatial.cutoff_support (tsupport_mul_subset_left h))
    rw [image_eq_zero_of_notMem_tsupport (fun h => hn (tsupport_iteratedFDeriv_subset r h)), norm_zero]
    positivity

lemma fixedPotential_scaled : Scaled (fun _ : Unit => fun _ => 1) (fun _ => Bounds.fixedPotential) :=
  ((cutoff_coordinate_scaled (fun _ : Unit => Construction.receiverIndex)).cmul
    (fun _ _ => zero_le_one) (-1) 1 (by norm_num)).congr (by intros; simp [Bounds.fixedPotential])

lemma Scaled.grow {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : A → ℕ → ℝ} (hs : ∀ a n, 1 ≤ s a n) {f : A → ℕ → E → F}
    (hf : Scaled (fun _ _ => 1) f) : Scaled s f := by
  obtain ⟨sf,B,hB,hfB⟩ := hf
  refine ⟨sf,B,hB,fun a r n x => ?_⟩
  have h : ‖iteratedFDeriv ℝ r (f a n) x‖ ≤ (B (a,r) : ℝ) := by simpa using hfB a r n x
  exact h.trans (le_mul_of_one_le_right (Nat.cast_nonneg _) (one_le_pow₀ (hs a n)))

lemma corePotential_scaled : Scaled (fun p : Machine × ℕ => Bounds.readScale p.1 p.2)
    (fun p => Bounds.corePotential p.1 p.2) := by
  have hs := fun p : Machine × ℕ => Bounds.readScale_nonneg p.1 p.2
  have h (idx : (Machine × ℕ) → ℕ → Fin 3) :=
    (cutoff_coordinate_scaled idx).grow (A := Machine × ℕ) (E := Space) (F := ℝ) (s := fun p => Bounds.readScale p.1 p.2) (fun p => Bounds.readScale_ge_one p.1 p.2)
  have hw := writeCore_scaled.coord hs (fun _ => Construction.donorIndex)
  have hh := (haltWeight_scaled.coord hs (fun _ => Construction.donorIndex)).cmul hs 2 2 (by norm_num)
  exact ((h (fun _ _ => 0)).mul (E := Space) hs hw).sub
    ((h (fun _ => Construction.receiverIndex)).mul (E := Space) hs hh)

end AlternatingNS.Effective

end ConstructiveBoundsDevelopment

end OAI
