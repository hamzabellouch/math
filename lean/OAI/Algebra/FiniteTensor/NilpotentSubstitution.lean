import Mathlib
import OAI.Algebra.FiniteTensor.NilpotentRoots
import OAI.Algebra.FiniteTensor.PolynomialApproximation

namespace OAI

/-! Algebraicity of full nilpotent substitution and the scalar equation systems. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.Spreading
noncomputable section
variable (K : Type*) [Field K] (m : ℕ) (τ : Type*)

abbrev SeriesFraction := FractionRing (MvPowerSeries τ K)

def seriesFractionParameters : MvPowerSeries τ (Parameters K m) →+*
    Parameters (SeriesFraction K τ) m :=
  (mapParameters (algebraMap (MvPowerSeries τ K) (SeriesFraction K τ))).comp
    (seriesParameterEquiv K m τ).toRingHom

 theorem boxCoeff_seriesFractionParameters (f : MvPowerSeries τ (Parameters K m)) (q : Box m) :
    boxCoeff (SeriesFraction K τ) m q (seriesFractionParameters K m τ f)=
      algebraMap (MvPowerSeries τ K) (SeriesFraction K τ) (boxSeries K m q f) := by
  rw [seriesFractionParameters,RingHom.comp_apply,RingEquiv.toRingHom_eq_coe,RingEquiv.coe_toRingHom,boxCoeff_mapParameters,
    boxCoeff_seriesParameterEquiv]

 theorem augmentation_seriesFractionParameters (f : MvPowerSeries τ (Parameters K m)) :
    augmentation (SeriesFraction K τ) m (seriesFractionParameters K m τ f)=
      algebraMap (MvPowerSeries τ K) (SeriesFraction K τ) (MvPowerSeries.map (augmentation K m) f) := by
  rw [seriesFractionParameters,RingHom.comp_apply,RingEquiv.toRingHom_eq_coe,RingEquiv.coe_toRingHom,augmentation_mapParameters,
    augmentation_seriesParameterEquiv]

 theorem seriesFractionParameters_map (f : MvPowerSeries τ K) :
    seriesFractionParameters K m τ (MvPowerSeries.map (algebraMap K (Parameters K m)) f)=
      algebraMap (SeriesFraction K τ) (Parameters (SeriesFraction K τ) m)
        (algebraMap (MvPowerSeries τ K) (SeriesFraction K τ) f) := by
  rw [seriesFractionParameters,RingHom.comp_apply,RingEquiv.toRingHom_eq_coe,RingEquiv.coe_toRingHom,seriesParameterEquiv_map,
    mapParameters_algebraMap]

 theorem map_augmentation_map (f : MvPowerSeries τ K) :
    MvPowerSeries.map (augmentation K m) (MvPowerSeries.map (algebraMap K (Parameters K m)) f)=f := by
  rw [MvPowerSeries.map_map]
  have h : (augmentation K m).comp (algebraMap K (Parameters K m))=RingHom.id K := by
    ext a
    exact augmentation_algebraMap K m a
  rw [h,MvPowerSeries.map_id,RingHom.id_apply]

variable {K m τ} {σ : Type*} [Finite σ] (H : σ → MvPowerSeries τ (Parameters K m))
  (hH : MvPowerSeries.HasSubst H)

 

def nilSubstitution : MvPowerSeries σ K →+* Parameters (SeriesFraction K τ) m :=
  (seriesFractionParameters K m τ).comp
    ((MvPowerSeries.substAlgHom (R:=Parameters K m) hH).toRingHom.comp
      (MvPowerSeries.map (algebraMap K (Parameters K m))))

omit [Finite σ] in
 theorem nilSubstitution_apply (f : MvPowerSeries σ K) :
    nilSubstitution H hH f=seriesFractionParameters K m τ
      (MvPowerSeries.subst H (MvPowerSeries.map (algebraMap K (Parameters K m)) f)) := by
  simp only [nilSubstitution,RingHom.comp_apply,AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom,MvPowerSeries.substAlgHom_apply]

omit [Finite σ] in
 theorem augmentation_nilSubstitution (j : σ ↪ τ)
    (hcentral : ∀ i,MvPowerSeries.map (augmentation K m) (H i)=MvPowerSeries.X (j i))
    (f : MvPowerSeries σ K) :
    augmentation (SeriesFraction K τ) m (nilSubstitution H hH f)=
      algebraMap (MvPowerSeries τ K) (SeriesFraction K τ) (MvPowerSeries.rename j f) := by
  rw [nilSubstitution_apply,augmentation_seriesFractionParameters,
    MvPowerSeries.map_subst hH,map_augmentation_map]
  congr 1
  rw [MvPowerSeries.rename_eq_subst]
  congr 1
  funext i
  exact hcentral i

omit [Finite σ] in
 theorem nilSubstitution_C (a : K) :
    nilSubstitution H hH (MvPowerSeries.C a)=
      algebraMap (SeriesFraction K τ) (Parameters (SeriesFraction K τ) m)
        (algebraMap (MvPowerSeries τ K) (SeriesFraction K τ) (MvPowerSeries.C a)) := by
  rw [nilSubstitution_apply,MvPowerSeries.map_C,MvPowerSeries.subst_C]
  rw [←MvPowerSeries.map_C,seriesFractionParameters_map]

omit [Finite σ] in
 theorem nilSubstitution_X (i : σ) :
    nilSubstitution H hH (MvPowerSeries.X i)=seriesFractionParameters K m τ (H i) := by
  rw [nilSubstitution_apply,MvPowerSeries.map_X,MvPowerSeries.subst_X hH]

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {m : ℕ} {σ τ : Type*} [Finite σ]

omit [CharZero K] in
 theorem algebraic_constant_series (a : K) :
    IsAlgebraic (MvPolynomial τ K) (MvPowerSeries.C (σ:=τ) a) := by
  simpa only [MvPowerSeries.algebraMap_apply',MvPowerSeries.map_id,
    Algebra.algebraMap_self,RingHom.id_apply,MvPolynomial.coe_C] using
    (isAlgebraic_algebraMap (R:=MvPolynomial τ K) (A:=MvPowerSeries τ K) (MvPolynomial.C a))

omit [CharZero K] in
 theorem algebraic_series_fraction_iff (f : MvPowerSeries τ K) :
    IsAlgebraic (MvPolynomial τ K)
      (algebraMap (MvPowerSeries τ K) (SeriesFraction K τ) f) ↔
        IsAlgebraic (MvPolynomial τ K) f :=
  isAlgebraic_algebraMap_iff (IsFractionRing.injective (MvPowerSeries τ K) (SeriesFraction K τ))

 

theorem algebraic_box_subst (H : σ → MvPowerSeries τ (Parameters K m))
    (hH : MvPowerSeries.HasSubst H)
    (hHalg : ∀ i q,IsAlgebraic (MvPolynomial τ K) (boxSeries K m q (H i)))
    (j : σ ↪ τ)
    (hcentral : ∀ i,MvPowerSeries.map (augmentation K m) (H i)=MvPowerSeries.X (j i))
    (f : MvPowerSeries σ K) (hf : IsAlgebraic (MvPolynomial σ K) f) (q : Box m) :
    IsAlgebraic (MvPolynomial τ K) (boxSeries K m q
      (MvPowerSeries.subst H (MvPowerSeries.map (algebraMap K (Parameters K m)) f))) := by
  classical
  let E := SeriesFraction K τ
  let k := algebraicSubfield (R:=MvPolynomial τ K) (E:=E)
  let F := nilSubstitution H hH
  let r : MvPolynomial σ K →+* Parameters E m :=
    F.comp (algebraMap (MvPolynomial σ K) (MvPowerSeries σ K))
  let B := (mapParameters (m:=m) k.subtype).range
  have hi : Function.Injective (algebraMap (MvPolynomial σ K) (MvPowerSeries σ K)) := by
    intro x y h
    apply MvPolynomial.coe_injective σ K
    simpa only [MvPowerSeries.algebraMap_apply',Algebra.algebraMap_self,
      MvPowerSeries.map_id,RingHom.id_apply] using h
  obtain ⟨P,_,hP,hD⟩ := exists_relation_derivative_ne_zero hi f hf
  have hHmem (i : σ) : seriesFractionParameters K m τ (H i)∈B := by
    apply (mem_parameter_range m k _).mpr
    intro b
    change IsAlgebraic (MvPolynomial τ K) _
    rw [boxCoeff_seriesFractionParameters,algebraic_series_fraction_iff]
    exact hHalg i b
  have hr (p : MvPolynomial σ K) : r p∈B := by
    induction p using MvPolynomial.induction_on with
    | C a =>
        have ha : algebraMap (MvPowerSeries τ K) E (MvPowerSeries.C a)∈k :=
          (algebraic_series_fraction_iff _).mpr (algebraic_constant_series a)
        refine ⟨algebraMap k (Parameters k m) ⟨_,ha⟩,?_⟩
        rw [mapParameters_algebraMap]
        change _=F (algebraMap (MvPolynomial σ K) (MvPowerSeries σ K) (MvPolynomial.C a))
        simp only [MvPowerSeries.algebraMap_apply',Algebra.algebraMap_self,
          MvPowerSeries.map_id,RingHom.id_apply,MvPolynomial.coe_C]
        exact (nilSubstitution_C H hH a).symm
    | add p q hp hq =>
        rw [map_add]
        exact B.add_mem hp hq
    | mul_X p i hp =>
        rw [map_mul]
        apply B.mul_mem hp
        change F (algebraMap (MvPolynomial σ K) (MvPowerSeries σ K) (MvPolynomial.X i))∈B
        simp only [MvPowerSeries.algebraMap_apply',Algebra.algebraMap_self,
          MvPowerSeries.map_id,RingHom.id_apply,MvPolynomial.coe_X]
        rw [show F (MvPowerSeries.X i)=seriesFractionParameters K m τ (H i) from nilSubstitution_X H hH i]
        exact hHmem i
  have ev (Q : Polynomial (MvPolynomial σ K)) :
      (Q.map r).eval (F f)=F (Polynomial.aeval f Q) := by
    change (Q.map (F.comp (algebraMap _ _))).eval (F f)=_
    rw [←Polynomial.map_map,Polynomial.eval_map_apply,Polynomial.eval_map,←Polynomial.aeval_def]
  have hroot : (P.map r).eval (F f)=0 := by rw [ev,hP,map_zero]
  have hconstant : IsAlgebraic (MvPolynomial τ K) (augmentation E m (F f)) := by
    rw [show augmentation E m (F f)=algebraMap (MvPowerSeries τ K) E (MvPowerSeries.rename j f)
      from augmentation_nilSubstitution H hH j hcentral f,algebraic_series_fraction_iff]
    exact algebraic_series_rename j j.injective f hf
  have hder : augmentation E m ((P.map r).derivative.eval (F f))≠0 := by
    rw [Polynomial.derivative_map,ev]
    rw [show augmentation E m (F (Polynomial.aeval f P.derivative))=
      algebraMap (MvPowerSeries τ K) E (MvPowerSeries.rename j (Polynomial.aeval f P.derivative))
      from augmentation_nilSubstitution H hH j hcentral _]
    intro hz
    apply hD
    apply MvPowerSeries.rename_injective j
    rw [map_zero]
    exact (IsFractionRing.injective (MvPowerSeries τ K) E) (by simpa only [map_zero] using hz)
  have halg := squarefree_root_algebraic (R:=MvPolynomial τ K) m (P.map r) (F f)
    (fun n b=>by
      rw [Polynomial.coeff_map]
      exact (mem_parameter_range m k _).mp (hr (P.coeff n)) b) hroot hconstant hder q
  change IsAlgebraic _ (boxCoeff E m q (nilSubstitution H hH f)) at halg
  rw [nilSubstitution_apply,boxCoeff_seriesFractionParameters,algebraic_series_fraction_iff] at halg
  exact halg

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open scoped BigOperators
variable (K : Type*) [Field K] (m : ℕ) (σ : Type*)

 

def algebraicBoxRing : Subring (MvPowerSeries σ (Parameters K m)) :=
  ((mapParameters (m:=m)
    (algebraicSubfield (R:=MvPolynomial σ K) (E:=SeriesFraction K σ)).subtype).range).comap
      (seriesFractionParameters K m σ)

 theorem mem_algebraicBoxRing (f : MvPowerSeries σ (Parameters K m)) :
    f∈algebraicBoxRing K m σ ↔
      ∀ q,IsAlgebraic (MvPolynomial σ K) (boxSeries K m q f) := by
  change seriesFractionParameters K m σ f∈
    (mapParameters (m:=m) (algebraicSubfield (R:=MvPolynomial σ K)
      (E:=SeriesFraction K σ)).subtype).range ↔ _
  rw [mem_parameter_range]
  apply forall_congr'
  intro q
  change IsAlgebraic (MvPolynomial σ K) (boxCoeff (SeriesFraction K σ) m q
    (seriesFractionParameters K m σ f)) ↔ _
  rw [boxCoeff_seriesFractionParameters]
  exact isAlgebraic_algebraMap_iff
    (IsFractionRing.injective (MvPowerSeries σ K) (SeriesFraction K σ))

 theorem boxSeries_C (q : Box m) (a : Parameters K m) :
    boxSeries K m q (MvPowerSeries.C (σ:=σ) a)=MvPowerSeries.C (boxCoeff K m q a) := by
  classical
  ext d
  simp only [coeff_boxSeries,MvPowerSeries.coeff_C]
  split <;> simp_all only [map_zero]

 theorem C_mem_algebraicBoxRing (a : Parameters K m) :
    MvPowerSeries.C (σ:=σ) a∈algebraicBoxRing K m σ := by
  apply (mem_algebraicBoxRing K m σ _).mpr
  intro q
  rw [boxSeries_C]
  simpa only [MvPowerSeries.algebraMap_apply',MvPowerSeries.map_id,
    Algebra.algebraMap_self,RingHom.id_apply,MvPolynomial.coe_C] using
      (isAlgebraic_algebraMap (R:=MvPolynomial σ K) (A:=MvPowerSeries σ K)
        (MvPolynomial.C (boxCoeff K m q a)))

 theorem map_mem_algebraicBoxRing (f : MvPowerSeries σ K)
    (hf : IsAlgebraic (MvPolynomial σ K) f) :
    MvPowerSeries.map (algebraMap K (Parameters K m)) f∈algebraicBoxRing K m σ := by
  let E := SeriesFraction K σ
  let k := algebraicSubfield (R:=MvPolynomial σ K) (E:=E)
  have hf' : algebraMap (MvPowerSeries σ K) E f∈k :=
    (isAlgebraic_algebraMap_iff
      (IsFractionRing.injective (MvPowerSeries σ K) E)).mpr hf
  refine ⟨algebraMap k (Parameters k m) ⟨_,hf'⟩,?_⟩
  rw [mapParameters_algebraMap]
  exact (seriesFractionParameters_map K m σ f).symm

 theorem assembleBox_mem_algebraicBoxRing (f : Box m → MvPowerSeries σ K)
    (hf : ∀q,IsAlgebraic (MvPolynomial σ K) (f q)) :
    assembleBox f∈algebraicBoxRing K m σ := by
  apply (mem_algebraicBoxRing K m σ _).mpr
  intro q
  rw [boxSeries_assembleBox]
  exact hf q

 theorem boxSeries_pderiv (i : σ) (q : Box m) (f : MvPowerSeries σ (Parameters K m)) :
    boxSeries K m q (MvPowerSeries.pderiv i f)=
      MvPowerSeries.pderiv i (boxSeries K m q f) := by
  ext d
  simp only [coeff_boxSeries,MvPowerSeries.coeff_pderiv]
  simpa only [nsmul_eq_mul,Nat.cast_add,Nat.cast_one,mul_comm] using
    (map_nsmul (boxCoeff K m q) (d i+1) (MvPowerSeries.coeff (d+Finsupp.single i 1) f))

variable [CharZero K]
 theorem pderiv_mem_algebraicBoxRing (i : σ) (f : MvPowerSeries σ (Parameters K m))
    (hf : f∈algebraicBoxRing K m σ) :
    MvPowerSeries.pderiv i f∈algebraicBoxRing K m σ := by
  apply (mem_algebraicBoxRing K m σ _).mpr
  intro q
  rw [boxSeries_pderiv]
  exact algebraic_series_pderiv i _ ((mem_algebraicBoxRing K m σ f).mp hf q)

variable {K m σ} {τ : Type*} [Finite σ]
 theorem subst_mem_algebraicBoxRing (H : σ → MvPowerSeries τ (Parameters K m))
    (hH : MvPowerSeries.HasSubst H)
    (hHalg : ∀i,H i∈algebraicBoxRing K m τ)
    (j : σ ↪ τ)
    (hcentral : ∀i,MvPowerSeries.map (augmentation K m) (H i)=MvPowerSeries.X (j i))
    (f : MvPowerSeries σ (Parameters K m)) (hf : f∈algebraicBoxRing K m σ) :
    MvPowerSeries.subst H f∈algebraicBoxRing K m τ := by
  classical
  rw [←assembleBox_boxSeries f,assembleBox,←MvPowerSeries.substAlgHom_apply hH,map_sum]
  apply Subring.sum_mem
  intro q _
  rw [map_mul,MvPowerSeries.substAlgHom_apply,MvPowerSeries.subst_C,
    MvPowerSeries.substAlgHom_apply]
  apply Subring.mul_mem _ (C_mem_algebraicBoxRing K m τ _)
  apply (mem_algebraicBoxRing K m τ _).mpr
  intro b
  exact algebraic_box_subst H hH
    (fun i b=>(mem_algebraicBoxRing K m τ _).mp (hHalg i) b) j hcentral _
    ((mem_algebraicBoxRing K m σ _).mp hf q) b

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
 theorem algebraic_variable_series {σ : Type*} (i : σ) :
    IsAlgebraic (MvPolynomial σ K) (MvPowerSeries.X (R:=K) i) := by
  simpa only [MvPowerSeries.algebraMap_apply',MvPowerSeries.map_id,
    Algebra.algebraMap_self,RingHom.id_apply,MvPolynomial.coe_X] using
      (isAlgebraic_algebraMap (R:=MvPolynomial σ K) (A:=MvPowerSeries σ K) (MvPolynomial.X i))

omit [CharZero K] in
 theorem algebraic_affineUnknown {σ : Type*} (i : σ) (a : K) :
    IsAlgebraic (MvPolynomial σ K) (affineUnknown i a) :=
  by
    unfold affineUnknown
    exact (algebraic_variable_series (K:=K) i).add (algebraic_constant_series (τ:=σ) a)

omit [CharZero K] in
 theorem algebraic_series_sum {σ ι : Type*} (s : Finset ι) (f : ι → MvPowerSeries σ K)
    (hf : ∀i∈s,IsAlgebraic (MvPolynomial σ K) (f i)) :
    IsAlgebraic (MvPolynomial σ K) (∑i∈s,f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (isAlgebraic_zero (R:=MvPolynomial σ K) (A:=MvPowerSeries σ K))
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).add (ih (fun j hj=>hf j (Finset.mem_insert_of_mem hj)))

omit [CharZero K] in
 theorem map_augmentation_eq_boxSeries_zero {σ : Type*} {m : ℕ}
    (f : MvPowerSeries σ (Parameters K m)) :
    MvPowerSeries.map (augmentation K m) f=boxSeries K m (fun _=>0) f := by
  ext d
  simp only [MvPowerSeries.coeff_map,coeff_boxSeries,augmentation_eq_boxCoeff_zero]

variable {l m d c : ℕ} {n : Fin l → ℕ}
  {e : ((i : Fin l) × Fin (n i)) ≃ Fin d ⊕ Fin c} {active : Fin m ↪ Fin l}
variable (M : TensorModel K (fun i=>Fin (n i)) m d c e active)
  (W : TensorPrimitives K (fun i=>Fin (n i)) m M)

omit [CharZero K] in
 theorem algebraic_potential
    (hF : ∀i,IsAlgebraic (MvPolynomial (Fin (n i)) K) (M.F i)) :
    IsAlgebraic (MvPolynomial ((i : Fin l) × Fin (n i)) K)
      (potential K (fun i=>Fin (n i)) M.F) := by
  apply algebraic_series_sum
  intro i _
  exact algebraic_series_rename (Sigma.mk i) (fun _ _ h=>eq_of_heq (Sigma.mk.inj h).2) _ (hF i)

omit [CharZero K] in
 theorem algebraic_perturbation
    (hb : ∀i,IsAlgebraic (MvPolynomial (Fin (n (active i))) K) (M.b i)) (j : Fin m) :
    IsAlgebraic (MvPolynomial ((i : Fin l) × Fin (n i)) K)
      (perturbation K (fun i=>Fin (n i)) m active M.b j) :=
  algebraic_series_rename (Sigma.mk (active j)) (fun _ _ h=>eq_of_heq (Sigma.mk.inj h).2) _ (hb j)

omit [CharZero K] in
 theorem deformed_mem_algebraicBoxRing
    (hF : ∀i,IsAlgebraic (MvPolynomial (Fin (n i)) K) (M.F i))
    (hb : ∀i,IsAlgebraic (MvPolynomial (Fin (n (active i))) K) (M.b i)) :
    deformed K (fun i=>Fin (n i)) m M.F active M.b∈
      algebraicBoxRing K m ((i : Fin l) × Fin (n i)) := by
  apply Subring.add_mem _ (map_mem_algebraicBoxRing K m _ _ (algebraic_potential M hF))
  apply Subring.sum_mem
  intro j _
  exact Subring.mul_mem _ (C_mem_algebraicBoxRing K m _ _)
    (map_mem_algebraicBoxRing K m _ _ (algebraic_perturbation M hb j))

omit [CharZero K] in
 theorem universalLeftH_mem_algebraicBoxRing (v : (i : Fin l) × Fin (n i)) :
    universalLeftH M v∈algebraicBoxRing K m (LeftUnknown ((i : Fin l) × Fin (n i)) m) :=
  assembleBox_mem_algebraicBoxRing K m _ _ (fun _=>algebraic_affineUnknown _ _)

omit [CharZero K] in
 theorem universalLeftP_mem_algebraicBoxRing (t : Triple m) (v : (i : Fin l) × Fin (n i)) :
    universalLeftP M W t v∈algebraicBoxRing K m (LeftUnknown ((i : Fin l) × Fin (n i)) m) :=
  assembleBox_mem_algebraicBoxRing K m _ _ (fun _=>algebraic_affineUnknown _ _)

 def leftCentralEmbedding : ((i : Fin l) × Fin (n i)) ↪ LeftUnknown ((i : Fin l) × Fin (n i)) m where
  toFun := fun v=>.inl (v,fun _=>0)
  inj' := fun _ _ h=>congrArg Prod.fst (Sum.inl.inj h)

omit [CharZero K] in
 theorem augmentation_universalLeftH (v : (i : Fin l) × Fin (n i)) :
    MvPowerSeries.map (augmentation K m) (universalLeftH M v)=
      MvPowerSeries.X (leftCentralEmbedding (m:=m) v) := by
  rw [map_augmentation_eq_boxSeries_zero,universalLeftH,boxSeries_assembleBox,affineUnknown]
  have hz : MvPowerSeries.constantCoeff (boxSeries K m (fun _=>0) (M.H v))=0 := by
    change boxCoeff K m (fun _=>0) (MvPowerSeries.constantCoeff (M.H v))=0
    rw [←augmentation_eq_boxCoeff_zero]
    exact (parameter_mem_iff_augmentation_zero K m _).mp (M.H_zero v)
  rw [hz,map_zero,add_zero]
  rfl

 theorem universalLeft_substitution_algebraic
    (f : MvPowerSeries ((i : Fin l) × Fin (n i)) (Parameters K m))
    (hf : f∈algebraicBoxRing K m ((i : Fin l) × Fin (n i))) :
    MvPowerSeries.subst (universalLeftH M) f∈
      algebraicBoxRing K m (LeftUnknown ((i : Fin l) × Fin (n i)) m) :=
  subst_mem_algebraicBoxRing _ (hasSubst_universalLeftH M)
    (universalLeftH_mem_algebraicBoxRing M) leftCentralEmbedding
    (augmentation_universalLeftH M) f hf

omit [CharZero K] in
 theorem universalRightG_eq_X (v : (i : Fin l) × Fin (n i)) :
    universalRightG M v = MvPowerSeries.X (.inl v) := by
  simp only [universalRightG,affineUnknown,M.G_zero,map_zero,add_zero]

omit [CharZero K] in
 theorem universalRight_substitution_algebraic
    (f : MvPowerSeries ((i : Fin l) × Fin (n i)) K)
    (hf : IsAlgebraic (MvPolynomial ((i : Fin l) × Fin (n i)) K) f) :
    IsAlgebraic (MvPolynomial (RightUnknown ((i : Fin l) × Fin (n i)) m) K)
      (MvPowerSeries.subst (universalRightG M) f) := by
  have h : universalRightG M=fun v=>MvPowerSeries.X (.inl v) := funext (universalRightG_eq_X M)
  rw [h]
  simpa only [MvPowerSeries.rename_eq_subst,Function.comp_def] using
    (algebraic_series_rename (τ:=RightUnknown ((i : Fin l) × Fin (n i)) m) Sum.inl Sum.inl_injective f hf)

 

theorem universalLeftEquation_algebraic
    (hF : ∀i,IsAlgebraic (MvPolynomial (Fin (n i)) K) (M.F i))
    (hb : ∀i,IsAlgebraic (MvPolynomial (Fin (n (active i))) K) (M.b i))
    (j : LeftEquation m) :
    IsAlgebraic (MvPolynomial (LeftUnknown ((i : Fin l) × Fin (n i)) m) K)
      (universalLeftEquation M W j) := by
  have hf := deformed_mem_algebraicBoxRing M hF hb
  rcases j with q|tq
  · exact (mem_algebraicBoxRing K m _ _).mp (universalLeft_substitution_algebraic M _ hf) q
  · apply (mem_algebraicBoxRing K m _ _).mp _ tq.2
    apply Subring.sub_mem _ _ (C_mem_algebraicBoxRing K m _ _)
    apply Subring.sum_mem
    intro v _
    exact Subring.mul_mem _ (universalLeftP_mem_algebraicBoxRing M W tq.1 v)
      (universalLeft_substitution_algebraic M _ (pderiv_mem_algebraicBoxRing K m _ v _ hf))

omit [CharZero K] in
theorem universalRightP_algebraic (t : Triple m) (v : (i : Fin l) × Fin (n i)) :
    IsAlgebraic (MvPolynomial (RightUnknown ((i : Fin l) × Fin (n i)) m) K)
      (universalRightP M W t v) := by
  unfold universalRightP
  exact algebraic_affineUnknown (σ:=RightUnknown ((i : Fin l) × Fin (n i)) m)
    (Sum.inr (t,v)) (MvPowerSeries.constantCoeff (W.right t v))

 theorem universalRightSummand_algebraic
    (hF : ∀i,IsAlgebraic (MvPolynomial (Fin (n i)) K) (M.F i))
    (t : Triple m) (v : (i : Fin l) × Fin (n i)) :
    IsAlgebraic (MvPolynomial (RightUnknown ((i : Fin l) × Fin (n i)) m) K)
      (universalRightP M W t v * MvPowerSeries.subst (universalRightG M)
        (MvPowerSeries.pderiv v (potential K (fun i=>Fin (n i)) M.F))) := by
  exact (universalRightP_algebraic M W t v).mul
    (universalRight_substitution_algebraic M _
      (algebraic_series_pderiv v _ (algebraic_potential M hF)))

 
theorem universalRightEquation_algebraic
    (hF : ∀i,IsAlgebraic (MvPolynomial (Fin (n i)) K) (M.F i))
    (hb : ∀i,IsAlgebraic (MvPolynomial (Fin (n (active i))) K) (M.b i))
    (j : RightEquation m) :
    IsAlgebraic (MvPolynomial (RightUnknown ((i : Fin l) × Fin (n i)) m) K)
      (universalRightEquation M W j) := by
  have hf := algebraic_potential M hF
  rcases j with u|t
  · exact universalRight_substitution_algebraic M _ hf
  · dsimp only [universalRightEquation,Sum.elim_inr]
    apply IsAlgebraic.sub
    · apply algebraic_series_sum
      intro v _
      exact universalRightSummand_algebraic M W hF t v
    · exact universalRight_substitution_algebraic M _
        (((algebraic_perturbation M hb t.val.1).mul (algebraic_perturbation M hb t.val.2.1)).mul
          (algebraic_perturbation M hb t.val.2.2))

end
end PD4Tensor.Spreading
end

end OAI
