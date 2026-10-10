import OAI.Analysis.PeriodicLattice.EffectiveForcing

namespace OAI

/-! Uniform force compilers and the complete periodic lattice memory theorem. -/

namespace PeriodicLattice

local instance finiteFunctionEncodingMain {n : ℕ} {A : Type*} [Encodable A] :
    Encodable (Fin n → A) := Encodable.finArrow

noncomputable section

namespace EffectiveFields
open CertifiedReal Quantitative RapidCalculus TorusCalculus RecursiveArithmetic
open scoped ContDiff
local instance mainLocal1 : Primcodable ℚ := ratPrimcodable
local instance mainLocal2 : DecidablePred Input.WellFormed := Classical.decPred _
local instance mainLocal3 : Primcodable ValidInput := Primcodable.subtype inputWellFormed

@[fun_prop] theorem mixedWord_recursive : Primrec (fun p : ℕ × MultiIndex => mixedWord p.1 p.2) := by
  have hr (i : Option (Fin 3)) : Primrec (fun n : ℕ => List.replicate n i) :=
    (Primrec.list_map Primrec.list_range (Primrec.const i).to₂).of_eq (fun n => by simp)
  have hα (i : Fin 3) : Primrec (fun p : ℕ × MultiIndex => p.2 i) :=
    Primrec.fin_app.comp Primrec.snd (Primrec.const i)
  exact (Primrec.list_append.comp (hr none |>.comp Primrec.fst)
    (Primrec.list_append.comp ((hr (some 2)).comp (hα 2))
      (Primrec.list_append.comp ((hr (some 1)).comp (hα 1)) ((hr (some 0)).comp (hα 0))))).of_eq
    (fun p => by simp only [mixedWord,spatialWord,List.append_assoc])

theorem uniformlyEffective_of_certificate {F : Input → VectorField}
    (hF : FieldCertificate F) (hf : ComponentsEffective F) : UniformlyEffective F := by
  obtain ⟨Q,hQ,bQ⟩ := word_evaluator hF hf
  let M : ValidInput × ℕ × MultiIndex × ℕ × ℕ → ℕ := fun p =>
    p.2.2.2.2 + hF.budget (p.1.1,mixedOrder p.2.1 p.2.2.1+1,0) + 6
  have hM : Primrec M := by
    have ha : Primrec (fun p : ValidInput × ℕ × MultiIndex × ℕ × ℕ => (p.2.1, p.2.2.1)) :=
      (Primrec.fst.comp Primrec.snd).pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    have ho : Primrec (fun p : ValidInput × ℕ × MultiIndex × ℕ × ℕ => mixedOrder p.2.1 p.2.2.1) :=
      (mixedOrder_recursive.comp ha).of_eq (fun _ => rfl)
    have hK : Primrec (fun p : ValidInput × ℕ × MultiIndex × ℕ × ℕ => hF.budget (p.1.1,mixedOrder p.2.1 p.2.2.1+1,0)) :=
      (hF.recursive.comp ((validData_recursive.comp Primrec.fst).pair
        ((Primrec.nat_add.comp ho (Primrec.const 1)).pair (Primrec.const 0)))).of_eq (fun _ => rfl)
    exact (Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))) hK) (Primrec.const 6)).of_eq (fun _ => rfl)
  let E : ValidInput × ℕ × MultiIndex × ℕ × ℕ × RationalPoint → Fin 3 → ℚ := fun p =>
    Q ((p.1,mixedWord p.2.1 p.2.2.1,p.2.2.2.2.2), 2^(p.2.2.2.2.1+6))
  have hE : Computable E := by
    have harg : Primrec (fun p : ValidInput × ℕ × MultiIndex × ℕ × ℕ × RationalPoint => (p.2.1, p.2.2.1)) :=
      (Primrec.fst.comp Primrec.snd).pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    have hw : Primrec (fun p : ValidInput × ℕ × MultiIndex × ℕ × ℕ × RationalPoint => mixedWord p.2.1 p.2.2.1) :=
      (mixedWord_recursive.comp harg).of_eq (fun _ => rfl)
    have hn : Primrec (fun p : ValidInput × ℕ × MultiIndex × ℕ × ℕ × RationalPoint => p.2.2.2.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    have ha : Primrec (fun p : ValidInput × ℕ × MultiIndex × ℕ × ℕ × RationalPoint => p.2.2.2.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    have hp : Primrec (fun p : ValidInput × ℕ × MultiIndex × ℕ × ℕ × RationalPoint =>
        ((p.1,mixedWord p.2.1 p.2.2.1,p.2.2.2.2.2),2^(p.2.2.2.2.1+6))) :=
      (Primrec.fst.pair (hw.pair ha)).pair (natPow.comp (Primrec.const 2) (Primrec.nat_add.comp hn (Primrec.const 6)))
    exact (hQ.comp hp.to_comp).of_eq (fun _ => rfl)
  obtain ⟨P,hP⟩ := program_of_computable hM.to_comp
  obtain ⟨R,hR⟩ := program_of_computable hE
  refine ⟨P,R,fun d hd r α T n => ?_⟩
  let v : ValidInput := ⟨d,hd⟩
  refine ⟨M (v,r,α,T,n), hP (v,r,α,T,n), fun a => ?_⟩
  refine ⟨E (v,r,α,T,n,a),hR (v,r,α,T,n,a),fun t x ht _hT hta hxa => ?_⟩
  rw [mixedD_eq_fieldWord (hF.smooth d) r α ht]
  have hlen : (mixedWord r α).length = mixedOrder r α := by
    simp [mixedWord,spatialWord,mixedOrder,Nat.add_assoc]
  have hb := fieldWord_nearby hF v (mixedWord r α) a ht x hta hxa
  rw [hlen] at hb
  calc
    _ ≤ ‖fieldWord (mixedWord r α) (F d) t (torusMk x) -
            fieldWord (mixedWord r α) (F d) (time a.1) (torusMk (rationalVector a.2))‖ +
        ‖fieldWord (mixedWord r α) (F d) (time a.1) (torusMk (rationalVector a.2)) - rationalVector (E (v,r,α,T,n,a))‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 4*(hF.budget (d,mixedOrder r α+1,0):ℝ)*accuracy (M (v,r,α,T,n)) + 3*error (2^(n+6)) :=
      add_le_add hb (bQ v (mixedWord r α) a (2^(n+6)))
    _ ≤ _ := evaluation_tolerance n _

end EffectiveFields

theorem periodic_lattice_memory (ν : ℝ) (hν : 0 < ν) (hνcomp : ComputableReal ν) :
    IsOpen detector ∧
    ∃ (U g f : Input → VectorField) (φ : Input → ScalarField)
      (C : Input → ℕ → MultiIndex → ℕ → ℕ),
      UniformlyEffective g ∧ UniformlyEffective f ∧ EffectiveConstants C ∧
      ∀ d : Input, d.WellFormed →
        LatticeConclusion ν d (U d) (g d) (f d) (φ d) (C d) := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖ν‖
  have hc := CertifiedReal.computableReal_effective hνcomp
  refine ⟨Detector.isOpen, FluidLift.velocity, FluidLift.force ν,
    FluidLift.solenoidalForce ν, FluidLift.potential, Quantitative.latticeConstants ν N hN,
    EffectiveFields.uniformlyEffective_of_certificate (Quantitative.forceCertificate ν N hN)
      (EffectiveFields.force_effective ν hc),
    EffectiveFields.uniformlyEffective_of_certificate (Quantitative.solenoidalForceCertificate ν N hN)
      (EffectiveFields.solenoidalForce_effective ν hc),
    Quantitative.latticeConstants_effective ν N hN, fun d hd => ?_⟩
  obtain ⟨C₀, hU, hg, hf, hφ, mU, mg, mf, mφ, eg, ef, _Rg, _Rf,
    sf, eφ, uφ, efφ, ug, uf, particle⟩ := FluidLift.analytic_lattice_conclusion ν hν.le d hd
  obtain ⟨Rg, Rf⟩ := Quantitative.latticeConstants_bounds ν N hN d hd
  exact ⟨hU, hg, hf, hφ, mU, mg, mf, mφ, eg, ef, Rg, Rf, sf, eφ, uφ, efφ, ug, uf, particle⟩

end
end PeriodicLattice

end OAI
