import OAI.NumberTheory.JointDickman.Amplification.ReducedRationalEquiv

namespace OAI

/-! # Rational arcs indexed by their finite lifts and period translates -/

namespace JointDickman

abbrev LiftedRationalData (j : ℕ) :=
  Σ q : ℕ+, (ZMod (q : ℕ))ˣ × (Fin j × ℤ)

noncomputable def liftedRationalEquiv (j : ℕ) [NeZero j] :
    LiftedRationalData j ≃ ℚ :=
  (Equiv.sigmaCongrRight (fun q : ℕ+ =>
    Equiv.prodCongr (Equiv.refl (ZMod (q : ℕ))ˣ)
      ((Equiv.prodComm (Fin j) ℤ).trans
        ((Equiv.prodCongr (Equiv.neg ℤ) (Equiv.refl (Fin j))).trans
          (Int.divModEquiv j).symm)))).trans
    (reducedRationalEquiv.trans (Equiv.neg ℚ))

theorem liftedRationalEquiv_den (j : ℕ) [NeZero j] (d : LiftedRationalData j) :
    (liftedRationalEquiv j d).den = (d.1 : ℕ) := by
  change (-reducedRationalValue _).den = _
  rw [Rat.neg_den, reducedRationalValue_den]
  rfl

theorem liftedRationalEquiv_cast (j : ℕ) [NeZero j] (q : ℕ+)
    (u : (ZMod (q : ℕ))ˣ) (t : Fin j) (k : ℤ) :
    (liftedRationalEquiv j ⟨q,u,t,k⟩ : ℝ) =
      -(j : ℝ)*((((u : ZMod (q : ℕ)).val : ℝ)/(q : ℕ)+t.val)/j-k) := by
  simp only [liftedRationalEquiv, Equiv.trans_apply, Equiv.sigmaCongrRight_apply,
    Equiv.prodCongr_apply, Prod.map_apply, Equiv.prodComm_apply, Prod.swap_prod_mk,
    Equiv.refl_apply, Int.divModEquiv_symm_apply, Equiv.neg_apply]
  have hv (d : ReducedRationalData) : reducedRationalEquiv d = reducedRationalValue d := rfl
  simp only [hv,reducedRationalValue]
  push_cast
  have hj : (j : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne j
  field_simp
  ring

end JointDickman

end OAI
