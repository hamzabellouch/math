import OAI.InformationTheory.SecretKey.Construction

namespace OAI

noncomputable section

namespace UnrestrictedQuantum

open Matrix MeasureTheory

open scoped ComplexOrder MatrixOrder

universe v3096_0 v3096_1 v3096_2 v3096_3 v3096_4

variable {A : Type v3096_0} {B : Type v3096_1} {C : Type v3096_2} [inst3096_0 : AddCommGroup A] [inst3096_1 : Module ℂ A] [inst3096_2 : One A]
  [inst3096_3 : AddCommGroup B] [inst3096_4 : Module ℂ B] [inst3096_5 : One B]
  [inst3096_6 : AddCommGroup C] [inst3096_7 : Module ℂ C] [inst3096_8 : One C]
  {ι : Type v3096_3} {κ : Type v3096_4} [inst3096_9 : Fintype ι] [inst3096_10 : Fintype κ] [inst3096_11 : DecidableEq ι] [inst3096_12 : DecidableEq κ]

def filterFunctional (K : Matrix κ ι ℂ) (S : ReferenceFunctional A ι) :
    ReferenceFunctional A κ where
  toFun x := K * S x * Kᴴ
  map_add' x y := by rw [map_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' z x := by simp only [map_smul, Matrix.mul_smul, Matrix.smul_mul,
    RingHom.id_apply]

omit inst3096_2 inst3096_5 inst3096_10 inst3096_11 inst3096_12 in
theorem filter_precompose [One A] [One B] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (K : Matrix κ ι ℂ) (S : ReferenceFunctional A ι)
    (L : B →ₗ[ℂ] A) :
    filterFunctional K (S.comp L) = (filterFunctional K S).comp L := rfl

omit inst3096_2 inst3096_5 inst3096_8 inst3096_10 inst3096_11 inst3096_12 in
theorem filter_precompose_two [One A] [One B] [One C] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (K : Matrix κ ι ℂ) (S : ReferenceFunctional A ι)
    (L : B →ₗ[ℂ] A) (M : C →ₗ[ℂ] B) :
    filterFunctional K ((S.comp L).comp M) =
      ((filterFunctional K S).comp L).comp M := rfl

omit inst3096_2 inst3096_11 inst3096_12 in
lemma filter_positive [One A] [DecidableEq ι] [DecidableEq κ] [LE A] (K : Matrix κ ι ℂ)
    {S : ReferenceFunctional A ι} (hS : PositiveFunctional S) :
    PositiveFunctional (filterFunctional K S) := by
  intro x hx
  exact (hS x hx).mul_mul_conjTranspose_same K

universe v3147_0

variable {O : Type v3147_0} [inst3147_0 : MeasurableSpace O] [inst3147_1 : LE A] [inst3147_2 : LE B]
  (J : ObservableInstrument O A B) (S : ReferenceFunctional A ι)

namespace InstrumentRun

variable (r : InstrumentRun J S)

omit inst3096_11 in
theorem event_reference [DecidableEq ι] (E : Set O) (hE : MeasurableSet E) :
    (fun i j => ∫ o in E, r.posterior o 1 i j ∂r.law) =
      S (J.operation E 1) := by
  ext i j
  exact r.update E hE 1 i j

omit inst3096_10 inst3096_11 inst3096_12 in
theorem filter_event [Fintype κ] [DecidableEq ι] [DecidableEq κ] (K : Matrix κ ι ℂ) (E : Set O) (hE : MeasurableSet E) :
    (fun i j => ∫ o in E, filterFunctional K (r.posterior o) 1 i j ∂r.law) =
      filterFunctional K S (J.operation E 1) := by
  ext i j
  simp only [filterFunctional, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.mul_apply, Finset.sum_mul]
  rw [integral_finsetSum _ (fun k _ =>
    integrable_finsetSum _ (fun l _ =>
      (((r.integrable 1 l k).const_mul (K i l)).mul_const (Kᴴ k j)).integrableOn))]
  simp_rw [integral_finsetSum _ (fun l _ =>
    (((r.integrable 1 l _).const_mul (K i l)).mul_const _).integrableOn),
    integral_mul_const, integral_const_mul, r.update E hE]

end InstrumentRun

end UnrestrictedQuantum

open MeasureTheory ProbabilityTheory Set Function unitInterval

open scoped ENNReal

namespace ZeroKey

universe v3238_0 v3238_1 v3238_2

theorem sample_instrument_update {S : Type v3238_0} {O : Type v3238_1} {Z : Type v3238_2} [MeasurableSpace S]
    [MeasurableSpace O] [StandardBorelSpace O] [Nonempty O] [MeasurableSpace Z]
    (κ : Kernel S O) [IsMarkovKernel κ]
    (update : S × O → Z) (hu : Measurable update) :
    ∃ f : S → I → O, Measurable (uncurry f) ∧
      ∀ (μ : Measure S) [IsFiniteMeasure μ],
        (μ.prod (volume : Measure I)).map (fun p => update (p.1, f p.1 p.2)) =
          (μ ⊗ₘ κ).map update := by
  obtain ⟨f,hf,_,hLaw⟩ := sample_instrument_kernel κ
  change Measurable (fun p : S × I => f p.1 p.2) at hf
  refine ⟨f,hf,?_⟩
  intro μ hμ
  rw [← hLaw μ, Measure.map_map hu (measurable_fst.prodMk hf)]
  rfl

lemma uniform_prefix_fresh_independent (n : ℕ) :
    IndepFun (fun u : UniformTape => fun i : Fin n => u i) (fun u => u n) uniformTapeLaw := by
  have h := iIndepFun_infinitePi (P := fun _ : ℕ => (volume : Measure I))
    (X := fun _ x => x) (fun _ => measurable_id)
  have hd : Disjoint (Finset.range n) {n} := by simp
  have hh := h.indepFun_finset (Finset.range n) {n} hd (fun i => measurable_pi_apply i)
  have hh' := hh.comp
    (show Measurable (fun x : (i : Finset.range n) → I => fun j : Fin n =>
      x ⟨j,Finset.mem_range.mpr j.isLt⟩) from by fun_prop)
    (show Measurable (fun x : (i : ({n} : Finset ℕ)) → I => x ⟨n,by simp⟩) from by fun_prop)
  exact hh'

lemma uniform_tape_eval (n : ℕ) : uniformTapeLaw.map (fun u => u n) = volume :=
  Measure.infinitePi_map_eval _ _

universe v3280_0

structure CausalSampler (O : Type v3280_0) [MeasurableSpace O] where
  step : (n : ℕ) → (Fin n → O) × I → O
  measurable_step : ∀ n, Measurable (step n)

namespace CausalSampler

universe v3285_0

variable {O : Type v3285_0} [inst3285_0 : MeasurableSpace O] (f : CausalSampler O)

def finiteHistory : (n : ℕ) → (Fin n → I) → (Fin n → O)
  | 0, _ => Fin.elim0
  | n+1, u => Fin.snoc (finiteHistory n (fun i => u i.castSucc))
      (f.step n (finiteHistory n (fun i => u i.castSucc), u (Fin.last n)))

lemma measurable_finiteHistory : ∀ n, Measurable (f.finiteHistory n) := by
  intro n
  induction n with
  | zero => exact Measurable.of_eval (fun i => Fin.elim0 i)
  | succ n ih =>
    have hr : Measurable (fun u : Fin (n+1) → I => fun i : Fin n => u i.castSucc) := by fun_prop
    apply Measurable.of_eval
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [finiteHistory, Fin.snoc_last,Function.comp_def] using
        (f.measurable_step n).comp ((ih.comp hr).prodMk (measurable_pi_apply (Fin.last n)))
    · simpa only [finiteHistory, Fin.snoc_castSucc,Function.comp_def] using (ih.comp hr).eval (a := j)

def history (n : ℕ) (u : UniformTape) : Fin n → O :=
  f.finiteHistory n (fun i => u i)

lemma measurable_prefix (n : ℕ) : Measurable (f.history n) :=
  (f.measurable_finiteHistory n).comp (by fun_prop)

lemma prefix_succ (n : ℕ) (u : UniformTape) :
    f.history (n+1) u = Fin.snoc (f.history n u) (f.step n (f.history n u,u n)) := rfl

lemma prefix_fresh_independent (n : ℕ) :
    IndepFun (f.history n) (fun u => u n) uniformTapeLaw :=
  (uniform_prefix_fresh_independent n).comp (f.measurable_finiteHistory n) measurable_id

lemma prefix_fresh_law (n : ℕ) :
    uniformTapeLaw.map (fun u => (f.history n u,u n)) =
      (uniformTapeLaw.map (f.history n)).prod volume := by
  rw [(f.prefix_fresh_independent n).map_prod_eq_prod_map_map
    (f.measurable_prefix n).aemeasurable (measurable_pi_apply n).aemeasurable,
    uniform_tape_eval]

theorem prefix_law_succ (κ : (n : ℕ) → Kernel (Fin n → O) O)
    [∀ n, IsMarkovKernel (κ n)]
    (hlaw : ∀ n s, volume.map (fun u => f.step n (s,u)) = κ n s)
    (n : ℕ) :
    uniformTapeLaw.map (f.history (n+1)) =
      ((uniformTapeLaw.map (f.history n)) ⊗ₘ κ n).map (fun p : (Fin n → O) × O => Fin.snoc (α := fun _ : Fin (n+1) => O) p.1 p.2) := by
  have hfresh := f.prefix_fresh_law n
  have hsample : ((uniformTapeLaw.map (f.history n)).prod (volume : Measure I)).map
      (fun p => (p.1, f.step n p)) = (uniformTapeLaw.map (f.history n)) ⊗ₘ κ n := by
    ext B hB
    rw [Measure.map_apply (measurable_fst.prodMk (f.measurable_step n)) hB,
      Measure.prod_apply (hB.preimage (measurable_fst.prodMk (f.measurable_step n))),
      Measure.compProd_apply hB]
    congr 1
    funext s
    have hm : Measurable (fun u : I => f.step n (s,u)) := by
      simpa only [Function.comp_def, id_eq] using
        ((f.measurable_step n).comp ((measurable_const (a := s)).prodMk measurable_id))
    rw [← hlaw n s, Measure.map_apply hm (measurable_prodMk_left hB)]
    rfl
  have hs : Measurable (fun p : (Fin n → O) × O => Fin.snoc (α := fun _ : Fin (n+1) => O) p.1 p.2) := by
    apply Measurable.of_eval
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using measurable_snd
    · simpa only [Fin.snoc_castSucc, Function.comp_def] using (measurable_pi_apply j).comp measurable_fst
  rw [← hsample, ← hfresh,
    Measure.map_map (measurable_fst.prodMk (f.measurable_step n))
      ((f.measurable_prefix n).prodMk (measurable_pi_apply n)),
    Measure.map_map hs ((measurable_fst.prodMk (f.measurable_step n)).comp
      ((f.measurable_prefix n).prodMk (measurable_pi_apply n)))]
  rfl

def record (u : UniformTape) (n : ℕ) : O := f.step n (f.history n u,u n)

lemma measurable_record : Measurable f.record :=
  Measurable.of_eval (fun n =>
    (f.measurable_step n).comp ((f.measurable_prefix n).prodMk (measurable_pi_apply n)))

lemma prefix_eq_record (n : ℕ) (u : UniformTape) (i : Fin n) :
    f.history n u i = f.record u i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rw [f.prefix_succ]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last,record, Fin.val_last]
    · simpa only [Fin.snoc_castSucc, Fin.val_castSucc] using ih j

theorem finite_law_unique (κ : (n : ℕ) → Kernel (Fin n → O) O)
    [∀ n, IsMarkovKernel (κ n)]
    (hlaw : ∀ n s, volume.map (fun u => f.step n (s,u)) = κ n s)
    (P : Measure (ℕ → O)) [IsProbabilityMeasure P]
    (hP : ∀ n, P.map (fun x => fun i : Fin (n+1) => x i) =
      ((P.map (fun x => fun i : Fin n => x i)) ⊗ₘ κ n).map
        (fun p : (Fin n → O) × O => Fin.snoc (α := fun _ : Fin (n+1) => O) p.1 p.2)) :
    ∀ n, P.map (fun x => fun i : Fin n => x i) = uniformTapeLaw.map (f.history n) := by
  intro n
  induction n with
  | zero =>
    have ht : (fun x : ℕ → O => fun i : Fin 0 => x i) = fun _ => Fin.elim0 := by
      funext x i
      exact Fin.elim0 i
    rw [ht]
    change P.map (fun _ : ℕ → O => Fin.elim0) =
      uniformTapeLaw.map (fun _ : UniformTape => Fin.elim0)
    simp
  | succ n ih => rw [hP n, ih, f.prefix_law_succ κ hlaw]

theorem record_law_unique (κ : (n : ℕ) → Kernel (Fin n → O) O)
    [∀ n, IsMarkovKernel (κ n)]
    (hlaw : ∀ n s, volume.map (fun u => f.step n (s,u)) = κ n s)
    (P : Measure (ℕ → O)) [IsProbabilityMeasure P]
    (hP : ∀ n, P.map (fun x => fun i : Fin (n+1) => x i) =
      ((P.map (fun x => fun i : Fin n => x i)) ⊗ₘ κ n).map
        (fun p : (Fin n → O) × O => Fin.snoc (α := fun _ : Fin (n+1) => O) p.1 p.2)) :
    P = uniformTapeLaw.map f.record := by
  let Q := uniformTapeLaw.map f.record
  have hQ : IsProbabilityMeasure Q := inferInstance
  apply IsProjectiveLimit.unique (P := fun J : Finset ℕ => Q.map J.restrict) ?_
    (show IsProjectiveLimit Q (fun J : Finset ℕ => Q.map J.restrict) from fun _ => rfl)
  intro J
  let n := J.sup id + 1
  let index : J → Fin n := fun j => ⟨j.1,Nat.lt_succ_of_le (Finset.le_sup (f := id) j.2)⟩
  let cut : (Fin n → O) → (J → O) := fun x j => x (index j)
  have hc : Measurable cut := by fun_prop
  have h := congrArg (fun ν : Measure (Fin n → O) => ν.map cut)
    (f.finite_law_unique κ hlaw P hP n)
  rw [Measure.map_map hc (by fun_prop), Measure.map_map hc (f.measurable_prefix n)] at h
  change P.map J.restrict = (uniformTapeLaw.map f.record).map J.restrict
  rw [Measure.map_map (Finset.measurable_restrict J) f.measurable_record]
  have heL : cut ∘ (fun x : ℕ → O => fun i : Fin n => x i) = J.restrict := rfl
  have heR : cut ∘ f.history n = J.restrict ∘ f.record := by
    funext u j
    exact f.prefix_eq_record n u (index j)
  rwa [heL,heR] at h

end CausalSampler

universe v3434_0

theorem exists_causal_sampler {O : Type v3434_0} [MeasurableSpace O]
    [StandardBorelSpace O] [Nonempty O]
    (κ : (n : ℕ) → Kernel (Fin n → O) O) [∀ n, IsMarkovKernel (κ n)] :
    ∃ f : CausalSampler O, ∀ n s, volume.map (fun u => f.step n (s,u)) = κ n s := by
  have h (n : ℕ) := sample_instrument_kernel (κ n)
  choose sample hmeas hlaw hrest using h
  exact ⟨⟨fun n p => sample n p.1 p.2, hmeas⟩, hlaw⟩

end ZeroKey

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal

namespace ZeroKey

section

universe v3447_0

variable {Ω : Type v3447_0} {mΩ : MeasurableSpace Ω} [inst3447_0 : StandardBorelSpace Ω]
  {μ : Measure Ω} [inst3447_1 : IsFiniteMeasure μ]

lemma condIndep_public_prefixes (ℱ : Filtration ℕ mΩ)
    (A B : MeasurableSpace Ω) (hA : A ≤ mΩ) (hB : B ≤ mΩ)
    (hinitial : CondIndep (ℱ 0) A B (ℱ.le 0) μ)
    (hlocal : ∀ n, ℱ (n+1) ≤ A ⊔ ℱ n ∨ ℱ (n+1) ≤ B ⊔ ℱ n) :
    ∀ n, CondIndep (ℱ n) A B (ℱ.le n) μ := by
  intro n
  induction n with
  | zero => exact hinitial
  | succ n ih =>
    rcases hlocal n with h | h
    · exact condIndep_local_message (ℱ.le n) hA hB (ℱ.mono (Nat.le_succ n)) h ih
    · exact (condIndep_local_message (ℱ.le n) hB hA (ℱ.mono (Nat.le_succ n)) h ih.symm).symm

end

open MeasureTheory ProbabilityTheory

universe v3676_0

variable {Ω : Type v3676_0} {mΩ : MeasurableSpace Ω} [inst3676_0 : StandardBorelSpace Ω]
  {μ : Measure Ω} [inst3676_1 : IsFiniteMeasure μ]

theorem independent_tapes_given_full_transcript (ℱ : Filtration ℕ mΩ)
    (A B : MeasurableSpace Ω) (hA : A ≤ mΩ) (hB : B ≤ mΩ)
    (hinitial : CondIndep (ℱ 0) A B (ℱ.le 0) μ)
    (hlocal : ∀ n, ℱ (n+1) ≤ A ⊔ ℱ n ∨ ℱ (n+1) ≤ B ⊔ ℱ n) :
    CondIndep (⨆ n, ℱ n) (A ⊔ ⨆ n, ℱ n) (B ⊔ ⨆ n, ℱ n)
      (iSup_le fun n => ℱ.le n) μ := by
  have h := condIndep_full_transcript ℱ A B hA hB
    (condIndep_public_prefixes ℱ A B hA hB hinitial hlocal)
  have hC := iSup_le fun n => ℱ.le n
  have h1 := (condIndep_join_public_right hC hB hA h.symm).symm
  exact condIndep_join_public_right hC (sup_le hA hC) hB h1

end ZeroKey

open MeasureTheory ProbabilityTheory Function Set

namespace ZeroKey

namespace LocalTapeProgram

universe v3724_0 v3724_1 v3724_2

variable {U : Type v3724_0} {V : Type v3724_1} {M : Type v3724_2} [inst3724_0 : MeasurableSpace U] [inst3724_1 : MeasurableSpace V] [inst3724_2 : MeasurableSpace M]
  (p : LocalTapeProgram U V M)

def message (n : ℕ) (ω : U × V) : M :=
  if p.alice n then p.sendA n (ω.1,p.publicPrefix n ω) else p.sendB n (ω.2,p.publicPrefix n ω)

lemma prefix_succ (n : ℕ) (ω : U × V) :
    p.publicPrefix (n+1) ω = Fin.snoc (p.publicPrefix n ω) (p.message n ω) := rfl

lemma measurable_prefix : ∀ n, Measurable (p.publicPrefix n) := by
  intro n
  induction n with
  | zero => exact Measurable.of_eval (fun i => Fin.elim0 i)
  | succ n ih =>
    apply Measurable.of_eval
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [publicPrefix, Fin.snoc_last]
      split
      · exact (p.measA n).comp (measurable_fst.prodMk ih)
      · exact (p.measB n).comp (measurable_snd.prodMk ih)
    · simpa only [publicPrefix, Fin.snoc_castSucc] using ih.eval (a := j)

lemma measurable_message (n : ℕ) : Measurable (p.message n) := by
  unfold message
  split
  · exact (p.measA n).comp (measurable_fst.prodMk (p.measurable_prefix n))
  · exact (p.measB n).comp (measurable_snd.prodMk (p.measurable_prefix n))

@[instance_reducible]
def field (n : ℕ) : MeasurableSpace (U × V) :=
  MeasurableSpace.comap (p.publicPrefix n) inferInstance

lemma field_le (n : ℕ) : p.field n ≤ (inferInstance : MeasurableSpace (U × V)) := (p.measurable_prefix n).comap_le

lemma field_mono : Monotone p.field := by
  apply monotone_nat_of_le_succ
  intro n
  have h : @Measurable (U × V) (Fin n → M) (p.field (n+1)) _ (p.publicPrefix n) := by
    let : MeasurableSpace (U × V) := p.field (n+1)
    apply Measurable.of_eval
    intro i
    have hh := (@Measurable.of_comap_le (U × V) (Fin (n+1) → M)
      (p.field (n+1)) _ (p.publicPrefix (n+1)) le_rfl).eval (a := i.castSucc)
    simpa only [publicPrefix, Fin.snoc_castSucc] using hh
  exact h.comap_le

def filtration : Filtration ℕ (inferInstance : MeasurableSpace (U × V)) where
  seq := p.field
  mono' := p.field_mono
  le' := p.field_le

lemma field_zero : p.field 0 = ⊥ := by
  exact MeasurableSpace.comap_const Fin.elim0

lemma field_local (n : ℕ) :
    p.field (n+1) ≤ MeasurableSpace.comap Prod.fst ‹MeasurableSpace U› ⊔ p.field n ∨
      p.field (n+1) ≤ MeasurableSpace.comap Prod.snd ‹MeasurableSpace V› ⊔ p.field n := by
  have hp {C : MeasurableSpace (U × V)} (hC : p.field n ≤ C) :
      @Measurable (U × V) (Fin n → M) C _ (p.publicPrefix n) := Measurable.of_comap_le hC
  have hf {C : MeasurableSpace (U × V)}
      (hC : MeasurableSpace.comap Prod.fst ‹MeasurableSpace U› ≤ C) :
      @Measurable (U × V) U C _ Prod.fst := Measurable.of_comap_le hC
  have hg {C : MeasurableSpace (U × V)}
      (hC : MeasurableSpace.comap Prod.snd ‹MeasurableSpace V› ≤ C) :
      @Measurable (U × V) V C _ Prod.snd := Measurable.of_comap_le hC
  cases ha : p.alice n
  · right
    let : MeasurableSpace (U × V) := MeasurableSpace.comap Prod.snd ‹MeasurableSpace V› ⊔ p.field n
    apply Measurable.comap_le
    apply Measurable.of_eval
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [publicPrefix, Fin.snoc_last, ha, Bool.false_eq_true, ↓reduceIte, Function.comp_def] using
        (p.measB n).comp ((hg le_sup_left).prodMk (hp le_sup_right))
    · simpa only [publicPrefix, Fin.snoc_castSucc] using (hp le_sup_right).eval (a := j)
  · left
    let : MeasurableSpace (U × V) := MeasurableSpace.comap Prod.fst ‹MeasurableSpace U› ⊔ p.field n
    apply Measurable.comap_le
    apply Measurable.of_eval
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [publicPrefix, Fin.snoc_last, ha, ↓reduceIte, Function.comp_def] using
        (p.measA n).comp ((hf le_sup_left).prodMk (hp le_sup_right))
    · simpa only [publicPrefix, Fin.snoc_castSucc] using (hp le_sup_right).eval (a := j)

theorem tapes_conditionally_independent [StandardBorelSpace U] [StandardBorelSpace V]
    (μ : Measure U) (ν : Measure V) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    CondIndep (⨆ n, p.field n)
      (MeasurableSpace.comap Prod.fst ‹MeasurableSpace U› ⊔ ⨆ n, p.field n)
      (MeasurableSpace.comap Prod.snd ‹MeasurableSpace V› ⊔ ⨆ n, p.field n)
      (iSup_le p.field_le) (μ.prod ν) := by
  apply independent_tapes_given_full_transcript p.filtration _ _
    measurable_fst.comap_le measurable_snd.comap_le
  · change CondIndep (p.field 0) _ _ _ _
    have h0 := indep_condIndep_bot measurable_fst.comap_le measurable_snd.comap_le
      (P := μ.prod ν) (indepFun_prod (μ := μ) (ν := ν) measurable_id measurable_id)
    simpa only [p.field_zero] using h0
  · exact p.field_local

def record (ω : U × V) (n : ℕ) : M := p.message n ω

lemma measurable_record : Measurable p.record :=
  Measurable.of_eval p.measurable_message

lemma prefix_eq_record (n : ℕ) (ω : U × V) (i : Fin n) :
    p.publicPrefix n ω i = p.record ω i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [publicPrefix, Fin.snoc_last, record, message, Fin.val_last]
    · simpa only [publicPrefix, Fin.snoc_castSucc, Fin.val_castSucc] using ih j

lemma full_record_field :
    MeasurableSpace.comap p.record inferInstance = ⨆ n, p.field n := by
  apply le_antisymm
  · let : MeasurableSpace (U × V) := ⨆ n, p.field n
    apply Measurable.comap_le
    apply Measurable.of_eval
    intro n
    have h : @Measurable (U × V) (Fin (n+1) → M) (⨆ n, p.field n) _
        (p.publicPrefix (n+1)) := Measurable.of_comap_le (le_iSup p.field (n+1))
    simpa only [publicPrefix, Fin.snoc_last, record, message] using h.eval (a := Fin.last n)
  · apply iSup_le
    intro n
    let : MeasurableSpace (U × V) := MeasurableSpace.comap p.record inferInstance
    apply Measurable.comap_le
    apply Measurable.of_eval
    intro i
    simp_rw [prefix_eq_record]
    exact (Measurable.of_comap_le (f := p.record) le_rfl).eval

universe v3866_0 v3866_1

theorem final_records_conditionally_independent
    [StandardBorelSpace U] [StandardBorelSpace V]
    (μ : Measure U) (ν : Measure V) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {A : Type v3866_0} {B : Type v3866_1} [MeasurableSpace A] [MeasurableSpace B]
    (readA : U × (ℕ → M) → A) (readB : V × (ℕ → M) → B)
    (ha : Measurable readA) (hb : Measurable readB) :
    CondIndepFun (MeasurableSpace.comap p.record inferInstance)
      p.measurable_record.comap_le
      (fun ω => readA (ω.1,p.record ω))
      (fun ω => readB (ω.2,p.record ω)) (μ.prod ν) := by
  have h := p.tapes_conditionally_independent μ ν
  rw [condIndepFun_iff_condIndep]
  have hA : MeasurableSpace.comap (fun ω => readA (ω.1,p.record ω)) inferInstance ≤
      MeasurableSpace.comap Prod.fst ‹MeasurableSpace U› ⊔ ⨆ n, p.field n := by
    apply Measurable.comap_le
    exact ha.comp ((Measurable.of_comap_le le_sup_left).prodMk
      (Measurable.of_comap_le (p.full_record_field ▸ le_sup_right)))
  have hB : MeasurableSpace.comap (fun ω => readB (ω.2,p.record ω)) inferInstance ≤
      MeasurableSpace.comap Prod.snd ‹MeasurableSpace V› ⊔ ⨆ n, p.field n := by
    apply Measurable.comap_le
    exact hb.comp ((Measurable.of_comap_le le_sup_left).prodMk
      (Measurable.of_comap_le (p.full_record_field ▸ le_sup_right)))
  have h' := condIndep_of_condIndep_of_le_right
    (condIndep_of_condIndep_of_le_left h hA) hB
  simpa only [p.full_record_field] using h'

end LocalTapeProgram

end ZeroKey

open MeasureTheory ProbabilityTheory Function Set unitInterval

namespace ZeroKey

theorem selected_tapes_law (alice : ℕ → Bool) :
    (uniformTapeLaw.prod uniformTapeLaw).map
      (fun uv : UniformTape × UniformTape => fun n => if alice n then uv.1 n else uv.2 n) =
      uniformTapeLaw := by
  let ν : Measure ((Fin 2 × ℕ) → I) :=
    Measure.infinitePi (fun _ => (volume : Measure I))
  let split : ((Fin 2 × ℕ) → I) → UniformTape × UniformTape :=
    fun u => (fun n => u (0,n), fun n => u (1,n))
  have hs : Measurable split := by fun_prop
  have hsplit : ν.map split = uniformTapeLaw.prod uniformTapeLaw := by
    have hc := Measure.infinitePi_map_curry (fun (_ : Fin 2) (_ : ℕ) => (volume : Measure I))
    change ν.map (MeasurableEquiv.curry (Fin 2) ℕ I) =
      Measure.infinitePi (fun _ : Fin 2 => uniformTapeLaw) at hc
    rw [Measure.infinitePi_eq_pi (fun _ : Fin 2 => uniformTapeLaw)] at hc
    have h := congrArg (fun P : Measure (Fin 2 → UniformTape) =>
      P.map MeasurableEquiv.finTwoArrow) hc
    rw [Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _),
      (measurePreserving_finTwoArrow uniformTapeLaw).map_eq] at h
    exact h
  let chooseTape : UniformTape × UniformTape → UniformTape :=
    fun uv n => if alice n then uv.1 n else uv.2 n
  have hm : Measurable chooseTape := by
    apply Measurable.of_eval
    intro n
    dsimp [chooseTape]
    split <;> fun_prop
  rw [← hsplit, Measure.map_map hm hs]
  let index : ℕ → Fin 2 × ℕ := fun n => (if alice n then 0 else 1,n)
  have hi : Injective index := by intro a b hab; exact congrArg Prod.snd hab
  have h := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : Fin 2 × ℕ => (volume : Measure I)) hi
  have he : chooseTape ∘ split = fun u n => u (index n) := by
    funext u n
    dsimp [chooseTape,split,index]
    split <;> rfl
  rw [he]
  exact h

namespace LocalOutcomeSampler

universe v3955_0 v3955_1

variable {O : Type v3955_0} {M : Type v3955_1} [inst3955_0 : MeasurableSpace O] [inst3955_1 : MeasurableSpace M]
  (p : LocalOutcomeSampler O M)

lemma measurable_privatePrefix (a : Bool) : ∀ n, Measurable (p.privatePrefix a n) := by
  intro n
  induction n with
  | zero => exact Measurable.of_eval (fun i => Fin.elim0 i)
  | succ n ih =>
    have hr : Measurable (fun pair : UniformTape × (Fin (n+1) → M) =>
      (pair.1,fun i : Fin n => pair.2 i.castSucc)) := by fun_prop
    have hv : Measurable (fun pair : UniformTape × (Fin (n+1) → M) =>
      fun i : Fin n => pair.2 i.castSucc) := by fun_prop
    apply Measurable.of_eval
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [privatePrefix,Fin.snoc_last]
      split
      · apply measurable_inl.comp
        split
        · exact (p.sampleA_meas n).comp (((ih.comp hr).prodMk hv).prodMk
            ((measurable_pi_apply n).comp measurable_fst))
        · exact (p.sampleB_meas n).comp (((ih.comp hr).prodMk hv).prodMk
            ((measurable_pi_apply n).comp measurable_fst))
      · exact measurable_const
    · simpa only [privatePrefix,Fin.snoc_castSucc,Function.comp_def] using
        (ih.comp hr).eval (a := j)

def tapeProgram : LocalTapeProgram UniformTape UniformTape M where
  alice := p.alice
  sendA n pair := p.sendA n ((p.privatePrefix true n pair,pair.2),
    p.sampleA n ((p.privatePrefix true n pair,pair.2),pair.1 n))
  sendB n pair := p.sendB n ((p.privatePrefix false n pair,pair.2),
    p.sampleB n ((p.privatePrefix false n pair,pair.2),pair.1 n))
  measA n := (p.sendA_meas n).comp
    (((p.measurable_privatePrefix true n).prodMk measurable_snd).prodMk
      ((p.sampleA_meas n).comp (((p.measurable_privatePrefix true n).prodMk measurable_snd).prodMk
        ((measurable_pi_apply n).comp measurable_fst))))
  measB n := (p.sendB_meas n).comp
    (((p.measurable_privatePrefix false n).prodMk measurable_snd).prodMk
      ((p.sampleB_meas n).comp (((p.measurable_privatePrefix false n).prodMk measurable_snd).prodMk
        ((measurable_pi_apply n).comp measurable_fst))))

def privateRecord (a : Bool) (pair : UniformTape × (ℕ → M)) (n : ℕ) : (O ⊕ Unit) :=
  if p.alice n = a then
    let past := fun i : Fin n => pair.2 i
    let privatePast := p.privatePrefix a n (pair.1,past)
    Sum.inl (if a then p.sampleA n ((privatePast,past),pair.1 n)
      else p.sampleB n ((privatePast,past),pair.1 n))
  else Sum.inr ()

lemma measurable_privateRecord (a : Bool) : Measurable (p.privateRecord a) := by
  apply Measurable.of_eval
  intro n
  have hp : Measurable (fun pair : UniformTape × (ℕ → M) => fun i : Fin n => pair.2 i) := by fun_prop
  have hl := (p.measurable_privatePrefix a n).comp (measurable_fst.prodMk hp)
  simp only [privateRecord]
  split
  · apply measurable_inl.comp
    split
    · exact (p.sampleA_meas n).comp ((hl.prodMk hp).prodMk
        ((measurable_pi_apply n).comp measurable_fst))
    · exact (p.sampleB_meas n).comp ((hl.prodMk hp).prodMk
        ((measurable_pi_apply n).comp measurable_fst))
  · exact measurable_const

universe v4032_0 v4032_1

theorem final_records_independent {A : Type v4032_0} {B : Type v4032_1} [MeasurableSpace A] [MeasurableSpace B]
    (readA : (ℕ → (O ⊕ Unit)) × (ℕ → M) → A)
    (readB : (ℕ → (O ⊕ Unit)) × (ℕ → M) → B)
    (ha : Measurable readA) (hb : Measurable readB) :
    CondIndepFun (MeasurableSpace.comap p.tapeProgram.record inferInstance)
      p.tapeProgram.measurable_record.comap_le
      (fun uv => readA (p.privateRecord true (uv.1,p.tapeProgram.record uv),p.tapeProgram.record uv))
      (fun uv => readB (p.privateRecord false (uv.2,p.tapeProgram.record uv),p.tapeProgram.record uv))
      (uniformTapeLaw.prod uniformTapeLaw) := by
  exact p.tapeProgram.final_records_conditionally_independent uniformTapeLaw uniformTapeLaw
    (fun pair => readA (p.privateRecord true pair,pair.2))
    (fun pair => readB (p.privateRecord false pair,pair.2))
    (ha.comp ((p.measurable_privateRecord true).prodMk measurable_snd))
    (hb.comp ((p.measurable_privateRecord false).prodMk measurable_snd))

lemma measurable_extractPrivate (a : Bool) (n : ℕ) :
    Measurable (p.extractPrivate a n) := by
  apply Measurable.of_eval
  intro i
  unfold extractPrivate
  split
  · exact measurable_inl.comp (measurable_pi_apply i)
  · exact measurable_const

lemma extractPrivate_snoc (a : Bool) (n : ℕ) (x : Fin n → O) (z : O) :
    p.extractPrivate a (n+1) (Fin.snoc (α := fun _ => O) x z) =
      Fin.snoc (p.extractPrivate a n x) (if p.alice n = a then Sum.inl z else Sum.inr ()) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [extractPrivate,Fin.snoc_last,Fin.val_last]
  · simp only [extractPrivate,Fin.snoc_castSucc,Fin.val_castSucc]

lemma measurable_publicFrom : ∀ n, Measurable (p.publicFrom n) := by
  intro n
  induction n with
  | zero => exact Measurable.of_eval (fun i => Fin.elim0 i)
  | succ n ih =>
    have hr : Measurable (fun x : Fin (n+1) → O => fun i : Fin n => x i.castSucc) := by fun_prop
    apply Measurable.of_eval
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [publicFrom,Fin.snoc_last]
      split
      · exact (p.sendA_meas n).comp ((((p.measurable_extractPrivate true n).comp hr).prodMk
          (ih.comp hr)).prodMk (measurable_pi_apply (Fin.last n)))
      · exact (p.sendB_meas n).comp ((((p.measurable_extractPrivate false n).comp hr).prodMk
          (ih.comp hr)).prodMk (measurable_pi_apply (Fin.last n)))
    · simpa only [publicFrom,Fin.snoc_castSucc,Function.comp_def] using (ih.comp hr).eval (a := j)

lemma publicFrom_snoc (n : ℕ) (x : Fin n → O) (z : O) :
    p.publicFrom (n+1) (Fin.snoc (α := fun _ => O) x z) =
      Fin.snoc (p.publicFrom n x) (if p.alice n then
        p.sendA n ((p.extractPrivate true n x,p.publicFrom n x),z) else
        p.sendB n ((p.extractPrivate false n x,p.publicFrom n x),z)) := by
  simp only [publicFrom,Fin.snoc_castSucc,Fin.snoc_last]

lemma privatePrefix_snoc (a : Bool) (n : ℕ) (u : UniformTape) (h : Fin n → M) (z : M) :
    p.privatePrefix a (n+1) (u,Fin.snoc (α := fun _ => M) h z) =
      Fin.snoc (p.privatePrefix a n (u,h)) (if p.alice n = a then Sum.inl
        (if a then p.sampleA n ((p.privatePrefix a n (u,h),h),u n)
        else p.sampleB n ((p.privatePrefix a n (u,h),h),u n)) else Sum.inr ()) := by
  simp only [privatePrefix,Fin.snoc_castSucc]

def causal : CausalSampler O where
  step n pair := if p.alice n then
    p.sampleA n ((p.extractPrivate true n pair.1,p.publicFrom n pair.1),pair.2) else
    p.sampleB n ((p.extractPrivate false n pair.1,p.publicFrom n pair.1),pair.2)
  measurable_step n := by
    split
    · exact (p.sampleA_meas n).comp ((((p.measurable_extractPrivate true n).comp measurable_fst).prodMk
        ((p.measurable_publicFrom n).comp measurable_fst)).prodMk measurable_snd)
    · exact (p.sampleB_meas n).comp ((((p.measurable_extractPrivate false n).comp measurable_fst).prodMk
        ((p.measurable_publicFrom n).comp measurable_fst)).prodMk measurable_snd)

def selectedTape (uv : UniformTape × UniformTape) (n : ℕ) : I :=
  if p.alice n then uv.1 n else uv.2 n

lemma measurable_selectedTape : Measurable p.selectedTape := by
  apply Measurable.of_eval
  intro n
  unfold selectedTape
  split <;> fun_prop

theorem replay_matches (n : ℕ) (uv : UniformTape × UniformTape) :
    p.publicFrom n (p.causal.history n (p.selectedTape uv)) = p.tapeProgram.publicPrefix n uv ∧
    ∀ a : Bool, p.extractPrivate a n (p.causal.history n (p.selectedTape uv)) =
      p.privatePrefix a n ((if a then uv.1 else uv.2),p.tapeProgram.publicPrefix n uv) := by
  induction n with
  | zero =>
    constructor
    · rfl
    · intro a; funext i; exact Fin.elim0 i
  | succ n ih =>
    have hs : p.causal.step n (p.causal.history n (p.selectedTape uv),p.selectedTape uv n) =
      if p.alice n then
        p.sampleA n ((p.privatePrefix true n (uv.1,p.tapeProgram.publicPrefix n uv),
          p.tapeProgram.publicPrefix n uv),uv.1 n) else
        p.sampleB n ((p.privatePrefix false n (uv.2,p.tapeProgram.publicPrefix n uv),
          p.tapeProgram.publicPrefix n uv),uv.2 n) := by
      change (if p.alice n then
        p.sampleA n ((p.extractPrivate true n (p.causal.history n (p.selectedTape uv)),
          p.publicFrom n (p.causal.history n (p.selectedTape uv))),p.selectedTape uv n)
        else p.sampleB n ((p.extractPrivate false n (p.causal.history n (p.selectedTape uv)),
          p.publicFrom n (p.causal.history n (p.selectedTape uv))),p.selectedTape uv n)) = _
      rw [ih.1,ih.2 true,ih.2 false]
      simp only [Bool.false_eq_true,↓reduceIte,selectedTape]
      split <;> simp_all only []
    rw [p.causal.prefix_succ,p.publicFrom_snoc,hs,ih.1,ih.2 true,ih.2 false]
    simp only [Bool.false_eq_true,↓reduceIte]
    constructor
    · rw [p.tapeProgram.prefix_succ]
      congr 1
      unfold LocalTapeProgram.message tapeProgram
      split <;> simp_all only [↓reduceIte]
    · intro a
      rw [p.extractPrivate_snoc,ih.2 a,p.tapeProgram.prefix_succ,p.privatePrefix_snoc]
      congr 1
      cases a <;> cases hrole : p.alice n <;>
        simp only [Bool.false_eq_true,Bool.true_eq_false,↓reduceIte]

def outcomeRecord (uv : UniformTape × UniformTape) : ℕ → O :=
  p.causal.record (p.selectedTape uv)

lemma measurable_outcomeRecord : Measurable p.outcomeRecord :=
  p.causal.measurable_record.comp p.measurable_selectedTape

lemma outcomeRecord_law (κ : (n : ℕ) → Kernel (Fin n → O) O)
    [∀ n, IsMarkovKernel (κ n)]
    (hlaw : ∀ n s, volume.map (fun u => p.causal.step n (s,u)) = κ n s)
    (P : Measure (ℕ → O)) [IsProbabilityMeasure P]
    (hP : ∀ n, P.map (fun x => fun i : Fin (n+1) => x i) =
      ((P.map (fun x => fun i : Fin n => x i)) ⊗ₘ κ n).map
        (fun pair : (Fin n → O) × O => Fin.snoc (α := fun _ : Fin (n+1) => O) pair.1 pair.2)) :
    (uniformTapeLaw.prod uniformTapeLaw).map p.outcomeRecord = P := by
  rw [p.causal.record_law_unique κ hlaw P hP]
  change (uniformTapeLaw.prod uniformTapeLaw).map (p.causal.record ∘ p.selectedTape) = _
  rw [← Measure.map_map p.causal.measurable_record p.measurable_selectedTape]
  congr 1
  exact selected_tapes_law p.alice

def publicRecord (x : ℕ → O) (n : ℕ) : M :=
  p.publicFrom (n+1) (fun i => x i) (Fin.last n)

def localRecord (a : Bool) (x : ℕ → O) (n : ℕ) : O ⊕ Unit :=
  if p.alice n = a then Sum.inl (x n) else Sum.inr ()

lemma measurable_publicRecord : Measurable p.publicRecord := by
  apply Measurable.of_eval
  intro n
  exact ((p.measurable_publicFrom (n+1)).comp (by fun_prop)).eval (a := Fin.last n)

lemma measurable_localRecord (a : Bool) : Measurable (p.localRecord a) := by
  apply Measurable.of_eval
  intro n
  unfold localRecord
  split
  · exact measurable_inl.comp (measurable_pi_apply n)
  · exact measurable_const

lemma publicRecord_replay (uv : UniformTape × UniformTape) :
    p.publicRecord (p.outcomeRecord uv) = p.tapeProgram.record uv := by
  funext n
  have h := congrFun (p.replay_matches (n+1) uv).1 (Fin.last n)
  have he : (fun i : Fin (n+1) => p.outcomeRecord uv i) =
      p.causal.history (n+1) (p.selectedTape uv) := by
    funext i
    exact (p.causal.prefix_eq_record (n+1) (p.selectedTape uv) i).symm
  change p.publicFrom (n+1) (fun i => p.outcomeRecord uv i) (Fin.last n) = _
  rw [he,h,p.tapeProgram.prefix_eq_record]
  rfl

lemma localRecord_replay (a : Bool) (uv : UniformTape × UniformTape) :
    p.localRecord a (p.outcomeRecord uv) =
      p.privateRecord a ((if a then uv.1 else uv.2),p.tapeProgram.record uv) := by
  funext n
  have h := congrFun ((p.replay_matches (n+1) uv).2 a) (Fin.last n)
  rw [p.causal.prefix_succ,p.extractPrivate_snoc,p.tapeProgram.prefix_succ,
    p.privatePrefix_snoc] at h
  simp only [Fin.snoc_last] at h
  have he : p.tapeProgram.publicPrefix n uv = fun i : Fin n => p.tapeProgram.record uv i := by
    funext i; exact p.tapeProgram.prefix_eq_record n uv i
  rw [he] at h
  exact h

universe v4239_0 v4239_1

theorem full_readout_law {A : Type v4239_0} {B : Type v4239_1} [MeasurableSpace A] [MeasurableSpace B]
    (κ : (n : ℕ) → Kernel (Fin n → O) O) [∀ n, IsMarkovKernel (κ n)]
    (hlaw : ∀ n s, volume.map (fun u => p.causal.step n (s,u)) = κ n s)
    (P : Measure (ℕ → O)) [IsProbabilityMeasure P]
    (hP : ∀ n, P.map (fun x => fun i : Fin (n+1) => x i) =
      ((P.map (fun x => fun i : Fin n => x i)) ⊗ₘ κ n).map
        (fun pair : (Fin n → O) × O => Fin.snoc (α := fun _ : Fin (n+1) => O) pair.1 pair.2))
    (readA : (ℕ → (O ⊕ Unit)) × (ℕ → M) → A)
    (readB : (ℕ → (O ⊕ Unit)) × (ℕ → M) → B)
    (ha : Measurable readA) (hb : Measurable readB) :
    P.map (fun x => (p.publicRecord x,
      readA (p.localRecord true x,p.publicRecord x),
      readB (p.localRecord false x,p.publicRecord x))) =
    (uniformTapeLaw.prod uniformTapeLaw).map (fun uv => (p.tapeProgram.record uv,
      readA (p.privateRecord true (uv.1,p.tapeProgram.record uv),p.tapeProgram.record uv),
      readB (p.privateRecord false (uv.2,p.tapeProgram.record uv),p.tapeProgram.record uv))) := by
  rw [← p.outcomeRecord_law κ hlaw P hP]
  have hm : Measurable (fun x => (p.publicRecord x,
      readA (p.localRecord true x,p.publicRecord x),
      readB (p.localRecord false x,p.publicRecord x))) := by
    exact p.measurable_publicRecord.prodMk
      ((ha.comp ((p.measurable_localRecord true).prodMk p.measurable_publicRecord)).prodMk
        (hb.comp ((p.measurable_localRecord false).prodMk p.measurable_publicRecord)))
  rw [Measure.map_map hm p.measurable_outcomeRecord]
  congr 1
  funext uv
  simp only [Function.comp_def,p.publicRecord_replay,p.localRecord_replay,
    Bool.false_eq_true,↓reduceIte]

end LocalOutcomeSampler

end ZeroKey

end

end OAI
