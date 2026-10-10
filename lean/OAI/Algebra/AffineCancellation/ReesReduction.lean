import OAI.Algebra.AffineCancellation.Degeneration
import OAI.Algebra.AffineCancellation.Rees

namespace OAI

noncomputable section

namespace ComplexCancellation.Rees
open MvPolynomial
def redValues : Fin 6 → Degeneration.G := ![0,Degeneration.p,Degeneration.s,
  Degeneration.u,Degeneration.F,Degeneration.J]
def redEval : Poly →ₐ[ℂ] Degeneration.G := aeval redValues
lemma redEval_relation : redEval relation=0 := by
  have h := Degeneration.relation_zero
  simpa [relation,xp,redEval,redValues,Degeneration.relation,Degeneration.xp,
    Degeneration.p,Degeneration.s,Degeneration.u,Degeneration.F,Degeneration.J,
    Matrix.cons_val,map_ofNat] using h
def red : B →ₐ[ℂ] Degeneration.G := Ideal.Quotient.liftₐ _ redEval (by
  intro r hr
  obtain ⟨t,rfl⟩ := Ideal.mem_span_singleton.mp hr
  rw [map_mul,redEval_relation,zero_mul])
@[simp] lemma red_π (r : Poly) : red (π r)=redEval r := Ideal.Quotient.lift_mk _ _ _
@[simp] lemma red_q : red q=0 := by simp [q,redEval,redValues]
abbrev Special := B ⧸ Ideal.span {q}
def ρ : B →ₐ[ℂ] Special := Ideal.Quotient.mkₐ ℂ _
def backRedValues : Fin 5 → Special := ![ρ (π (X 1)),ρ (π (X 2)),ρ (π (X 3)),
  ρ (π (X 4)),ρ (π (X 5))]
def backRedEval : Degeneration.P →ₐ[ℂ] Special := aeval backRedValues
lemma ρ_q : ρ q=0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
lemma backRedEval_relation : backRedEval Degeneration.relation=0 := by
  have h := congrArg ρ relation_zero
  have hq := ρ_q
  change ρ (π (X 0))=0 at hq
  simp only [relation,xp,map_sub,map_mul,map_add,map_pow,map_one,map_ofNat,hq] at h
  norm_num at h
  simp only [backRedEval,backRedValues,Degeneration.relation,Degeneration.xp,aeval_X,map_sub,map_mul,map_add,map_pow,map_one,map_ofNat,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
  linear_combination h
def backRed : Degeneration.G →ₐ[ℂ] Special := Ideal.Quotient.liftₐ _ backRedEval (by
  intro r hr
  obtain ⟨t,rfl⟩ := Ideal.mem_span_singleton.mp hr
  simp only [map_mul,backRedEval_relation]
  ring)
@[simp] lemma backRed_π (r : Degeneration.P) : backRed (Degeneration.π r)=backRedEval r :=
  Ideal.Quotient.lift_mk _ _ _
lemma backRed_red : backRed.comp red=ρ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change backRed (red (π (X i)))=ρ (π (X i))
  fin_cases i <;>
    simp [redEval,redValues,backRedEval,backRedValues,Matrix.cons_val,
      Degeneration.p,Degeneration.s,Degeneration.u,Degeneration.F,Degeneration.J]
  exact ρ_q.symm
lemma red_zero_iff (r : B) : red r=0 ↔ q ∣ r := by
  constructor
  · intro hr
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change ρ r=0
    rw [← backRed_red]
    simp [hr]
  · rintro ⟨s,rfl⟩
    simp
lemma q_not_isUnit : ¬IsUnit q := by
  intro h
  have := h.map red.toMonoidHom
  change IsUnit (red q) at this
  rw [red_q] at this
  exact not_isUnit_zero this
lemma maximum_q_factor {r : B} (hr : r ≠ 0) :
    ∃ (n : ℕ) (s : B), red s ≠ 0 ∧ r=q^n*s := by
  let : WfDvdMonoid B := IsNoetherianRing.wfDvdMonoid
  obtain ⟨n,s,hs,he⟩ := WfDvdMonoid.max_power_factor' hr q_not_isUnit
  exact ⟨n,s,mt (red_zero_iff s).mp hs,he⟩
end ComplexCancellation.Rees

end

end OAI
