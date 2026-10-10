import OAI.MathematicalPhysics.RapidForcing.AnalyticResult
import OAI.MathematicalPhysics.RapidForcing.BoundsPrograms
import OAI.MathematicalPhysics.RapidForcing.EvaluatorPrograms

namespace OAI

section
open Encodable Nat.Partrec
open scoped BigOperators
namespace RapidForcing
open EffectiveArithmetic

abbrev BoundQuery := ℕ × ℕ × ℕ × ℕ × ℕ
abbrev BoundParameters := RawInput × ℚ

def boundTable (p : BoundParameters × BoundQuery) : ℕ :=
  ⌈2^p.2.1 * forceJetBound (RawMachine.scaleData p.1.1.1 p.1.1.2) p.1.2
    p.2.1 (p.2.2.1 + p.2.2.2.1 + p.2.2.2.2.1 + p.2.2.2.2.2)⌉₊

attribute [local irreducible] forceJetBound velocityJetBound RawMachine.scaleData

@[fun_prop] lemma computable_boundTable : Computable boundTable := by
  let F (p : BoundParameters × BoundQuery) :=
    forceJetBound (RawMachine.scaleData p.1.1.1 p.1.1.2) p.1.2
      p.2.1 (p.2.2.1 + p.2.2.2.1 + p.2.2.2.2.1 + p.2.2.2.2.2)
  have hf : Computable F := by
    unfold F
    apply computable_forceJetBound.comp (g := fun p : BoundParameters × BoundQuery =>
      (RawMachine.scaleData p.1.1.1 p.1.1.2, p.1.2, p.2.1,
        p.2.2.1 + p.2.2.2.1 + p.2.2.2.2.1 + p.2.2.2.2.2))
    apply Computable.pair
    · exact RawMachine.computable_scaleData.comp (Computable.fst.comp Computable.fst)
    · fun_prop
  have hw : Computable (fun p : BoundParameters × BoundQuery => (2:ℚ)^p.2.1) := by fun_prop
  exact (computable_rat_natCeil.comp (computable_rat_mul.comp (hw.pair hf))).of_eq (fun _ => rfl)

noncomputable def boundsProgram (p : BoundParameters) : Program :=
  (typedCode (fun p => Part.some (boundTable p)) computable_boundTable.partrec).curry (encode p)

@[fun_prop] lemma computable_boundsProgram : Computable boundsProgram :=
  computable_specialize.comp ((Computable.const _).pair Computable.id)

lemma boundsProgram_eval (p : BoundParameters) (q : BoundQuery) :
    (boundsProgram p).eval (encode q) = Part.some (boundTable (p,q)) := by
  rw [boundsProgram, Code.eval_curry, ← encode_prod_val]
  exact (typedCode_eval (fun a => Part.some (boundTable a)) computable_boundTable.partrec (p,q)).trans rfl

lemma boundsProgram_spec (ν : ℝ) (νBound : ℚ) (hν : ‖ν‖ ≤ (νBound:ℝ))
    (M : Machine) (w : M.Input) :
    BoundsMixed (boundsProgram ((M.description, w.map Fin.val), νBound))
      (addressedForce ν M w) := by
  intro J l α
  let C := boundTable (((M.description, w.map Fin.val), νBound),
    (J, l, α 0, α 1, α 2))
  refine ⟨C, ?_, ?_⟩
  · rw [boundQuery, boundsProgram_eval]
    exact Part.mem_some _
  · intro t ht x
    have hb := (addressedForce_jetControl ν νBound hν M w).mixed_bound J l α t ht x
    apply hb.trans
    dsimp [C, boundTable]
    rw [Machine.description_scaleData]
    exact_mod_cast (Nat.le_ceil (2^J * forceJetBound (M.scaleData w) νBound J
      (l+α 0+α 1+α 2)))

def decodeInput (n : ℕ) : RawInput :=
  (decode n).getD ((1,1,0,[]), [])

@[fun_prop] lemma computable_decodeInput : Computable decodeInput :=
  Computable.option_getD Computable.decode (Computable.const _)

@[simp] lemma decodeInput_description (M : Machine) (w : M.Input) :
    decodeInput (M.inputDescription w) = (M.description, w.map Fin.val) := by
  simp [decodeInput, Machine.inputDescription]

noncomputable def forceCompiler (visc : Program) (νBound : ℚ) (n : ℕ) : ℕ × ℕ :=
  (encode (evaluationProgram (decodeInput n, visc)),
   encode (boundsProgram (decodeInput n, νBound)))

lemma computable_forceCompiler (visc : Program) (νBound : ℚ) :
    Computable (forceCompiler visc νBound) := by
  apply Computable.pair
  · exact Computable.encode.comp (computable_evaluationProgram.comp
      (computable_decodeInput.pair (Computable.const visc)))
  · exact Computable.encode.comp (computable_boundsProgram.comp
      (computable_decodeInput.pair (Computable.const νBound)))

@[simp] lemma ofNatCode_encode (c : Program) : Code.ofNatCode (encode c) = c :=
  Denumerable.ofNat_encode c

lemma forceCompiler_spec (ν : ℝ) (visc : Program) (hν : NamesReal visc ν)
    (νBound : ℚ) (hb : ‖ν‖ ≤ (νBound:ℝ)) (M : Machine) (w : M.Input) :
    ForceProgram (forceCompiler visc νBound (M.inputDescription w)) (addressedForce ν M w) := by
  simp only [ForceProgram, forceCompiler, ofNatCode_encode, decodeInput_description]
  exact ⟨evaluationProgram_spec ν visc hν M w, boundsProgram_spec ν νBound hb M w⟩

lemma computableReal_norm_bound (ν : ℝ) (visc : Program) (hν : NamesReal visc ν) :
    ∃ q : ℚ, ‖ν‖ ≤ (q:ℝ) := by
  obtain ⟨q, _, he⟩ := hν 0
  refine ⟨|q|+1, ?_⟩
  have h := norm_add_le (ν-(q:ℝ)) (q:ℝ)
  simp only [sub_add_cancel, Real.norm_eq_abs, abs_sub_comm ν (q:ℝ)] at h
  simp only [accuracy, pow_zero] at he
  rw [Rat.cast_add, Rat.cast_abs, Rat.cast_one, Real.norm_eq_abs]
  linarith

theorem addressed_effective (ν : ℝ) (hνcomp : ComputableReal ν) :
    ∃ compile : ℕ → ℕ × ℕ, Computable compile ∧ ∀ (M : Machine) (w : M.Input),
      ForceProgram (compile (M.inputDescription w)) (addressedForce ν M w) := by
  obtain ⟨visc,hν⟩ := hνcomp
  obtain ⟨νBound, hb⟩ := computableReal_norm_bound ν visc hν
  exact ⟨forceCompiler visc νBound, computable_forceCompiler visc νBound,
    forceCompiler_spec ν visc hν νBound hb⟩

theorem compact_support_rapid_decay (ν : ℝ) (hν : 0 < ν)
    (hνcomp : ComputableReal ν) :
    ∃ compile : ℕ → ℕ × ℕ, Computable compile ∧
      ∀ (M : Machine) (w : M.Input),
        let u := addressedVelocity M w
        let f := addressedForce ν M w
        ForceProgram (compile (M.inputDescription w)) f ∧
        Smooth f ∧ Supported f ∧ Rapid f ∧ RapidSpaceTime f ∧
        Smooth u ∧ Supported u ∧ Rapid u ∧ RapidSpaceTime u ∧
        UniqueEnergySolution ν f u (fun _ _ => 0) ∧
        ∃ X : ℝ → Space → Space, MaterialFlow u X ∧
          (M.Halts w ↔ ∃ t : ℝ, 0 ≤ t ∧ (X t 0) 0 < -1) := by
  obtain ⟨compile, hc, hf⟩ := addressed_effective ν hνcomp
  exact ⟨compile, hc, fun M w => ⟨hf M w, addressed_analytic_realization ν hν M w⟩⟩
end RapidForcing

end

end OAI
