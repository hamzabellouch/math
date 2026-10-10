import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.EffectiveArithmetic
import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.ResidualRegularity
import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.OracleComputability

namespace OAI

noncomputable section
namespace BalancedTransport.Geometry

lemma fullMixedD_add {v w : Velocity} (hv : JointSmooth v) (hw : JointSmooth w)
    (a : MultiIndex) : fullMixedD a (fun t x => v t x + w t x) =
      fun t x => fullMixedD a v t x + fullMixedD a w t x := by
  induction a with
  | nil => rfl
  | cons i a ih =>
    cases i with
    | none =>
      simp only [fullMixedD, ih]
      ext t x k
      rw [fullTimeD, deriv_fun_add (((hv.fullMixedD a).timeSlice x).differentiable (by simp) t)
        (((hw.fullMixedD a).timeSlice x).differentiable (by simp) t)]
      rfl
    | some i =>
      simp only [fullMixedD, ih]
      ext t x k
      rw [spaceD, fderiv_fun_add (((hv.fullMixedD a).slice t).differentiable (by simp) x)
        (((hw.fullMixedD a).slice t).differentiable (by simp) x)]
      rfl

lemma fullMixedD_smul (v : Velocity) (c : ℝ) (a : MultiIndex) :
    fullMixedD a (fun t x => c • v t x) = fun t x => c • fullMixedD a v t x := by
  induction a with
  | nil => rfl
  | cons i a ih =>
    cases i with
    | none =>
      simp only [fullMixedD, ih]
      ext t x k
      rw [fullTimeD, deriv_fun_const_smul_field]
      rfl
    | some i =>
      simp only [fullMixedD, ih]
      ext t x k
      change fderiv ℝ (c • fullMixedD a v t) x _ k = _
      rw [fderiv_const_smul_field]
      rfl

lemma mixedD_affineForce_of_extensions {v w V W : Velocity}
    (hv : JointSmooth V) (hw : JointSmooth W) (hev : ForwardEq V v) (hew : ForwardEq W w)
    (c : ℝ) (a : MultiIndex) (t : ℝ) (ht : 0 ≤ t) (x : Space) :
    mixedD a (affineForce v w c) t x = mixedD a v t x + c • mixedD a w t x := by
  have hcw : JointSmooth (fun t x => c • W t x) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × Space => c • W z.1 z.2)
    exact (contDiff_const (c := c)).smul hw
  have hadd : JointSmooth (fun t x => V t x + c • W t x) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × Space => V z.1 z.2 + c • W z.1 z.2)
    exact hv.add hcw
  have he : ForwardEq (fun t x => V t x + c • W t x) (affineForce v w c) := by
    intro t ht
    funext x
    change V t x + c • W t x = v t x + c • w t x
    rw [hev t ht, hew t ht]
  rw [← congrFun ((he.mixedD a) t ht) x,
    ← fullMixedD_eq_mixedD hadd a t ht x, fullMixedD_add hv hcw,
    fullMixedD_smul]
  dsimp only
  rw [fullMixedD_eq_mixedD hv a t ht x,
    fullMixedD_eq_mixedD hw a t ht x,
    congrFun ((hev.mixedD a) t ht) x, congrFun ((hew.mixedD a) t ht) x]

end BalancedTransport.Geometry
end

noncomputable section
namespace BalancedTransport.Effectivity

lemma error_nonneg (n : ℕ) : 0 ≤ error n := by unfold error; positivity

lemma error_le_one (n : ℕ) : error n ≤ 1 := by
  exact pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num)

lemma error_add (n k : ℕ) : error (n + k) = error n * error k := pow_add _ _ _

lemma nat_mul_error_shift (n k : ℕ) : (k : ℝ) * error (n + k) ≤ error n := by
  have hk : (k : ℝ) ≤ (2 : ℝ) ^ k := by
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [Nat.cast_succ, pow_succ]
      have hp : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      linarith
  have he : (k : ℝ) * error k ≤ 1 := by
    unfold error
    rw [inv_pow, ← div_eq_mul_inv]
    exact (div_le_one (by positivity)).mpr hk
  rw [error_add]
  nlinarith [mul_le_mul_of_nonneg_left he (error_nonneg n)]

lemma family_effective_field {v : Family Velocity} (hv : EffectiveFamily v)
    (M : FiniteMachine) (w : Input M) (O : Set (ℕ →. ℕ)) : EffectiveFieldIn O (v M w) := by
  obtain ⟨E, b, R, hE, hb, _, heval, hbound, _⟩ := hv
  refine ⟨(fun s => E (inputCode M w, s)), (fun a => b (inputCode M w, a)),
    (hE.comp ((Computable.const _).pair Computable.id)).computableIn,
    (hb.comp ((Computable.const _).pair Computable.id)).computableIn, ?_, ?_⟩
  · intro a z n hz i
    exact heval M w a z n hz i
  · intro a t ht x
    exact hbound M w a t ht x

lemma realName_oracle_computable (name : ℕ → ℚ) :
    ComputableIn {nameOracle name} name := by
  have h := Nat.RecursiveIn.oracle (O := {nameOracle name}) (nameOracle name) (Set.mem_singleton _)
  change Nat.RecursiveIn {nameOracle name} (fun n => Part.some (Encodable.encode (name n))) at h
  have hr := Nat.RecursiveIn.comp (Primrec.nat_iff.mp primrec_ratRank).recursiveIn h
  apply Nat.RecursiveIn.of_eq hr
  intro n
  simp only [Part.bind_some, Encodable.decode_nat,
    Part.coe_some, Part.map_some]
  change (Part.some (rawRatCode (name n))).bind (fun k => Part.some (ratRank k)) = _
  rw [Part.bind_some]
  exact congrArg Part.some (ratRank_code (name n))

lemma computableIn_rat_add {α : Type*} [Primcodable α] {O : Set (ℕ →. ℕ)}
    {f g : α → ℚ} (hf : ComputableIn O f) (hg : ComputableIn O g) :
    ComputableIn O (fun a => f a + g a) :=
  computableIn_comp (O := O) (f := fun p : ℚ × ℚ => p.1 + p.2) (g := fun a => (f a, g a))
    (Computable.computableIn computable_rat_add) (computableIn_pair hf hg)

lemma computableIn_rat_mul {α : Type*} [Primcodable α] {O : Set (ℕ →. ℕ)}
    {f g : α → ℚ} (hf : ComputableIn O f) (hg : ComputableIn O g) :
    ComputableIn O (fun a => f a * g a) :=
  computableIn_comp (O := O) (f := fun p : ℚ × ℚ => p.1 * p.2) (g := fun a => (f a, g a))
    (Computable.computableIn computable_rat_mul) (computableIn_pair hf hg)

theorem effective_affine_force {O : Set (ℕ →. ℕ)} {v w : Velocity} {ν : ℝ}
    (hv : EffectiveFieldIn O v) (hw : EffectiveFieldIn O w)
    {name : ℕ → ℚ} (hc : ComputableIn O name) (hn : RealName name ν)
    (hlin : ∀ a t, 0 ≤ t → ∀ x,
      mixedD a (affineForce v w ν) t x = mixedD a v t x + ν • mixedD a w t x) :
    EffectiveFieldIn O (affineForce v w ν) := by
  obtain ⟨E₀, b₀, hE₀, hb₀, he₀, hbound₀⟩ := hv
  obtain ⟨E₁, b₁, hE₁, hb₁, he₁, hbound₁⟩ := hw
  obtain ⟨C, hC⟩ := exists_nat_ge |ν|
  let prec : MultiIndex × RationalPoint × ℕ → ℕ := fun s => s.2.2 + (C + b₁ s.1 + 2)
  have hb₁' : ComputableIn O (fun s : MultiIndex × RationalPoint × ℕ => b₁ s.1) :=
    computableIn_comp hb₁ ComputableIn.fst
  have hprec : ComputableIn O prec := by
    exact computableIn_comp₂ Primrec.nat_add.computableIn₂
      (computableIn_comp ComputableIn.snd ComputableIn.snd)
      (computableIn_comp₂ Primrec.nat_add.computableIn₂
        (computableIn_comp₂ Primrec.nat_add.computableIn₂ (ComputableIn.const C) hb₁')
        (ComputableIn.const 2))
  let arg : MultiIndex × RationalPoint × ℕ → MultiIndex × RationalPoint × ℕ :=
    fun s => (s.1, s.2.1, prec s)
  have harg : ComputableIn O arg := computableIn_pair ComputableIn.fst
    (computableIn_pair (computableIn_comp ComputableIn.fst ComputableIn.snd) hprec)
  let E : MultiIndex × RationalPoint × ℕ → Fin 3 → ℚ :=
    fun s i => E₀ (arg s) i + name (prec s) * E₁ (arg s) i
  have hi (i : Fin 3) : ComputableIn O (fun s => E s i) := by
    have h₀ : ComputableIn O (fun s => E₀ (arg s) i) :=
      computableIn_fin_eval (computableIn_comp hE₀ harg) i
    have h₁ : ComputableIn O (fun s => E₁ (arg s) i) :=
      computableIn_fin_eval (computableIn_comp hE₁ harg) i
    have hn' : ComputableIn O (fun s => name (prec s)) := computableIn_comp hc hprec
    exact computableIn_rat_add h₀ (computableIn_rat_mul hn' h₁)
  have hE : ComputableIn O E := by
    refine computableIn_of_eq (computableIn_fin_triple _ _ _ (hi 0) (hi 1) (hi 2)) ?_
    intro s
    ext i
    fin_cases i <;> rfl
  let b : MultiIndex → ℕ := fun a => b₀ a + C * b₁ a
  have hb : ComputableIn O b := computableIn_comp₂ Primrec.nat_add.computableIn₂ hb₀
    (computableIn_comp₂ Primrec.nat_mul.computableIn₂ (ComputableIn.const C) hb₁)
  refine ⟨E, b, hE, hb, ?_, ?_⟩
  · intro a z n hz i
    let k := prec (a,z,n)
    have h₀ := he₀ a z k hz i
    have h₁ := he₁ a z k hz i
    have hν := hn k
    have hνb : |(name k : ℝ)| ≤ C + 1 := by
      have htriangle : |(name k : ℝ)| ≤ |(name k : ℝ) - ν| + |ν| := by
        simpa only [sub_add_cancel] using abs_add_le ((name k : ℝ) - ν) ν
      linarith [error_le_one k]
    have hwval : |mixedD a w (z.1 : ℝ) (rationalSpace z.2) i| ≤ b₁ a :=
      (norm_le_pi_norm _ i).trans (hbound₁ a _ (by exact_mod_cast hz) _)
    have hid : (E (a,z,n) i : ℝ) -
        mixedD a (affineForce v w ν) (z.1 : ℝ) (rationalSpace z.2) i =
        ((E₀ (a,z,k) i : ℝ) - mixedD a v (z.1 : ℝ) (rationalSpace z.2) i) +
        (name k : ℝ) * ((E₁ (a,z,k) i : ℝ) - mixedD a w (z.1 : ℝ) (rationalSpace z.2) i) +
        ((name k : ℝ) - ν) * mixedD a w (z.1 : ℝ) (rationalSpace z.2) i := by
      rw [hlin a _ (by exact_mod_cast hz)]
      dsimp [E, arg, k]
      push_cast
      ring
    rw [hid]
    calc
      _ ≤ (error k + (C + 1) * error k) + error k * (b₁ a : ℝ) := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · refine (abs_add_le _ _).trans (add_le_add h₀ ?_)
          rw [abs_mul]
          exact mul_le_mul hνb h₁ (abs_nonneg _) (by positivity)
        · rw [abs_mul]
          exact mul_le_mul hν hwval (abs_nonneg _) (error_nonneg k)
      _ = (C + b₁ a + 2 : ℕ) * error (n + (C + b₁ a + 2)) := by
        dsimp [k, prec]
        push_cast
        ring
      _ ≤ error n := nat_mul_error_shift n _
  · intro a t ht x
    rw [hlin a t ht x]
    calc
      _ ≤ ‖mixedD a v t x‖ + ‖ν • mixedD a w t x‖ := norm_add_le _ _
      _ ≤ (b₀ a : ℝ) + C * (b₁ a : ℝ) := by
        apply add_le_add (hbound₀ a t ht x)
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul hC (hbound₁ a t ht x) (norm_nonneg _) (Nat.cast_nonneg _)
      _ = (b a : ℝ) := by simp [b]

theorem effective_viscosity_clauses {v w V W : Velocity}
    (hv : Geometry.JointSmooth V) (hw : Geometry.JointSmooth W)
    (hev : Geometry.ForwardEq V v) (hew : Geometry.ForwardEq W w)
    (ev : EffectiveFieldIn ∅ v) (ew : EffectiveFieldIn ∅ w) (ν : ℝ) :
    (ComputableReal ν → EffectiveFieldIn ∅ (affineForce v w ν)) ∧
    (∀ name : ℕ → ℚ, RealName name ν →
      EffectiveFieldIn {nameOracle name} (affineForce v w ν)) := by
  have hlin := Geometry.mixedD_affineForce_of_extensions hv hw hev hew ν
  constructor
  · rintro ⟨name, hc, hn⟩
    exact effective_affine_force ev ew hc.computableIn hn hlin
  · intro name hn
    have lift {f : Velocity} (hf : EffectiveFieldIn ∅ f) (O : Set (ℕ →. ℕ)) :
        EffectiveFieldIn O f := by
      obtain ⟨E,b,hE,hb,heval,hbound⟩ := hf
      refine ⟨E,b,?_,?_,heval,hbound⟩
      · exact hE.mono (Set.empty_subset O)
      · exact hb.mono (Set.empty_subset O)
    exact effective_affine_force (lift ev _) (lift ew _)
      (realName_oracle_computable name) hn hlin

theorem residual_effective_viscosity {U : Family Velocity}
    (hU : ∀ M w, Geometry.JointSmooth (U M w))
    (ef₀ : EffectiveFamily (fun M w => inertialCoefficient (U M w)))
    (ef₁ : EffectiveFamily (fun M w => viscousCoefficient (U M w)))
    (M : FiniteMachine) (w : Input M) (ν : ℝ) :
    (ComputableReal ν → EffectiveFieldIn ∅
      (affineForce (inertialCoefficient (U M w)) (viscousCoefficient (U M w)) ν)) ∧
    (∀ name : ℕ → ℚ, RealName name ν → EffectiveFieldIn {nameOracle name}
      (affineForce (inertialCoefficient (U M w)) (viscousCoefficient (U M w)) ν)) :=
  effective_viscosity_clauses (hU M w).fullInertial (hU M w).viscousCoefficient
    (Geometry.fullInertial_forwardEq (hU M w)) (fun _ _ => rfl)
    (family_effective_field ef₀ M w ∅) (family_effective_field ef₁ M w ∅) ν

end BalancedTransport.Effectivity
end

end OAI
