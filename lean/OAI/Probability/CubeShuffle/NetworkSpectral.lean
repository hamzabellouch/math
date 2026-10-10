import OAI.Probability.CubeShuffle.ExceptionalOperators
import OAI.RepresentationTheory.FiniteUnitary.KernelBounds
import OAI.RepresentationTheory.YoungSymmetry.UnitaryModel
import OAI.Probability.CubeShuffle.DimensionEstimates

namespace OAI

namespace CubeShuffle.UnitaryFinite
open scoped BigOperators Classical

lemma tupleAction_kernel {α ι : Type*} [Fintype ι] [DecidableEq α]
    {Ω : Type*} [Fintype Ω] (P : Ω → Equiv.Perm α)
    (e f : ι ↪ α) : actionKernel tupleAction P e f=PairRouting.tupleProbability P e f := by
  unfold actionKernel PairRouting.tupleProbability
  congr 1
  funext ω
  congr 1
  exact propext Function.Embedding.ext_iff

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
lemma full_tuple_fixed (d : ℕ) (ρ : Representation ℂ (Equiv.Perm (Card d)) V) :
    fixedSpace tupleAction (Function.Embedding.refl (Card d)) ρ=⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro v g hg
  have he : g=1 := by
    apply Equiv.ext
    intro x
    exact congrArg (fun f : Card d ↪ Card d => f x) hg
  rw [he,map_one]
  rfl

omit [FiniteDimensional ℂ V] in
lemma full_tuple_finrank (d : ℕ) (ρ : Representation ℂ (Equiv.Perm (Card d)) V) :
    Module.finrank ℂ (fixedSpace tupleAction (Function.Embedding.refl (Card d)) ρ)=Module.finrank ℂ V := by
  rw [full_tuple_fixed,finrank_top]

theorem palindrome_irrep_amplification (d : ℕ) {ι : Type*} [Fintype ι]
    (f : ι ↪ Card d) (hk : 0<Fintype.card ι)
    (ρ : Representation ℂ (Equiv.Perm (Card d)) V) [Representation.IsIrreducible ρ]
    (hρ : IsUnitary ρ) (hm : 0<Module.finrank ℂ (fixedSpace tupleAction f ρ))
    (z : ℝ) (hz : 0<z) :
    ‖sampleOperator ρ (palindromePerm d)‖ ≤
      Real.exp (densityConstant*Fintype.card ι*((Fintype.card ι:ℝ)/(2:ℝ)^d)^(1/512:ℝ))*
        z^(-(1/1000:ℝ))+Real.sqrt (z/(Module.finrank ℂ (fixedSpace tupleAction f ρ):ℝ)) := by
  apply sampleOperator_amplification tupleAction f (tupleAction_transitive f) ρ hρ
    (palindromePerm d) _ _ (1/1000) z _ (by norm_num) hz (by positivity) _ hm
  · intro e f
    simp only [tupleAction_kernel]
    exact palindrome_kernel_symmetric d e f
  · intro e
    simp only [tupleAction_kernel]
    exact PairRouting.tupleProbability_row_sum _ e
  · intro e
    simp only [tupleAction_kernel]
    exact palindrome_row_moment_bound d e hk

theorem modified_irrep_amplification (L r : ℕ) (E : Finset (Card r))
    (ρ : Representation ℂ (Equiv.Perm (Card (L+r))) V) [Representation.IsIrreducible ρ]
    (hρ : IsUnitary ρ) (hm : 0<Module.finrank ℂ V)
    (u z : ℝ) (hz : 0<z)
    (hM : ∀ e : Card (L+r) ↪ Card (L+r), modifiedRowMoment L r E e (1/1000)≤Real.exp u) :
    ‖sampleOperator ρ (modifiedPerm L r E)‖ ≤
      Real.exp u*z^(-(1/1000:ℝ))+Real.sqrt (z/(Module.finrank ℂ V:ℝ)) := by
  let f := Function.Embedding.refl (Card (L+r))
  have h := sampleOperator_amplification tupleAction f (tupleAction_transitive f) ρ hρ
    (modifiedPerm L r E) (fun e f => by simpa only [tupleAction_kernel] using modified_kernel_symmetric L r E e f)
    (fun e => by simpa only [tupleAction_kernel] using PairRouting.tupleProbability_row_sum (modifiedPerm L r E) e)
    (1/1000) z (Real.exp u) (by norm_num) hz (by positivity)
    (fun e => by simpa only [tupleAction_kernel,modifiedRowMoment] using hM e)
    (by simpa only [f,full_tuple_finrank] using hm)
  simpa only [f,full_tuple_finrank] using h

end CubeShuffle.UnitaryFinite

namespace CubeShuffle.UnitaryFinite
open scoped BigOperators Classical
open DimensionEstimates
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem full_palindrome_decay (d : ℕ)
    (ρ : Representation ℂ (Equiv.Perm (Card d)) V) [Representation.IsIrreducible ρ]
    (hρ : IsUnitary ρ) (hm : 0<Module.finrank ℂ V)
    (hden : densityConstant*(2:ℝ)^d≤Real.log (Module.finrank ℂ V)/4000)
    (hl : 8000*Real.log 2≤Real.log (Module.finrank ℂ V)) :
    ‖sampleOperator ρ (palindromePerm d)‖≤Real.exp (-Real.log (Module.finrank ℂ V)/8000) := by
  have h := palindrome_irrep_amplification d (Function.Embedding.refl (Card d))
    (Fintype.card_pos) ρ hρ (by simpa only [full_tuple_finrank] using hm)
    (Real.exp (Real.log (Module.finrank ℂ V)/2)) (Real.exp_pos _)
  simp only [full_tuple_finrank,card_positions,Nat.cast_pow,Nat.cast_ofNat,
    div_self (by positivity : (2:ℝ)^d≠0),Real.one_rpow,mul_one] at h
  exact h.trans (amplification_decay _ _ (by exact_mod_cast hm) hden hl)

theorem full_modified_decay (L r : ℕ) (E : Finset (Card r))
    (ρ : Representation ℂ (Equiv.Perm (Card (L+r))) V) [Representation.IsIrreducible ρ]
    (hρ : IsUnitary ρ) (hm : 0<Module.finrank ℂ V) (u : ℝ)
    (hM : ∀ e : Card (L+r) ↪ Card (L+r), modifiedRowMoment L r E e (1/1000)≤Real.exp u)
    (hden : u≤Real.log (Module.finrank ℂ V)/4000)
    (hl : 8000*Real.log 2≤Real.log (Module.finrank ℂ V)) :
    ‖sampleOperator ρ (modifiedPerm L r E)‖≤Real.exp (-Real.log (Module.finrank ℂ V)/8000) := by
  exact (modified_irrep_amplification L r E ρ hρ hm u
    (Real.exp (Real.log (Module.finrank ℂ V)/2)) (Real.exp_pos _) hM).trans
    (amplification_decay _ _ (by exact_mod_cast hm) hden hl)

lemma palindrome_exception_cards (r L : ℕ)
    (ρ : Representation ℂ (Equiv.Perm (Card (L+r))) V) (hρ : IsUnitary ρ) (n : ℕ) :
    ‖sampleOperator ρ (palindromePerm (L+r))‖ ≤
      (blockGap L)^n+∑ E : Finset (Card r), if E.card<n then
        ‖sampleOperator ρ (modifiedPerm L r E)‖ else 0 := by
  let σ := ρ.comp (splitPerm r L).symm.toMonoidHom
  have he : σ.comp (splitPerm r L).toMonoidHom=ρ := by
    ext g v
    change ρ ((splitPerm r L).symm ((splitPerm r L) g)) v=ρ g v
    rw [MulEquiv.symm_apply_apply]
  have h := palindrome_exception_bound r L σ (unitary_comp ρ hρ _) n
  simpa only [he] using h

end CubeShuffle.UnitaryFinite

end OAI
