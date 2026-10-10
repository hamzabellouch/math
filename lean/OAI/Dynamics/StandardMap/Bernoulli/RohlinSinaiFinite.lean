import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Bernoulli.ReverseFano

namespace OAI

section
section
namespace HyperbolicCoding
open StandardMapEntropy.Entropy MeasureTheory Set Filter
open scoped Topology ENNReal
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
variable {A B : Type*} [Fintype A] [Fintype B]
variable [MeasurableSpace A] [MeasurableSpace B]
variable [MeasurableSingletonClass A] [MeasurableSingletonClass B] [Nonempty B]

theorem zero_entropy_opposite_factor (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (p : X → A) (q : X → B) (hp : Measurable p) (hq : Measurable q)
    (hz : rate μ e q=0)
    (hfactor : ∃ F : (ℕ → A) → B,Measurable F ∧ q=ᵐ[μ]F ∘ tailName e.symm p 0) :
    TailObservable μ e p q := by
  intro m
  apply exists_factor_of_approx μ (tailName e p m) q
  intro ε hε
  obtain ⟨M,hM⟩ := exists_cond_prefix_lt μ (measurable_tailName e.symm.measurable hp 0) hq
    hfactor (ε/2) (half_pos hε)
  change cond μ q (word e.symm p M)<ε/2 at hM
  let n := M+m+1
  let qS := q ∘ e^[M]
  have hqS : Measurable qS := hq.comp (e.measurable.iterate M)
  have hqz : rate μ e qS=0 := (rate_comp_iterate μ e he q hq M).trans hz
  let g₀ (v : Fin n → A) (i : Fin M) := v ⟨M-i.val,by dsimp [n]; omega⟩
  have hg₀ : g₀ ∘ word e p n=(word e.symm p M) ∘ e^[M] := by
    funext x i
    change p (e^[M-i.val] x)=p (e.symm^[i.val] (e^[M] x))
    rw [inverse_iterate_forward_sub e (by omega)]
  have hP : cond μ qS (word e p n)≤cond μ q (word e.symm p M) := by
    have hh := cond_factor_right μ qS (word e p n) g₀ hqS (word_measurable e e.measurable p hp n)
    rw [hg₀] at hh
    exact hh.trans_eq (cond_comp_preserving μ (e^[M]) (he.iterate M) q (word e.symm p M)
      hq (word_measurable e.symm e.symm.measurable p hp M))
  have hsmall : cond μ qS (word e p n)<ε := lt_trans (hP.trans_lt hM) (by linarith)
  have ht : Tendsto (fun L : ℕ => cond μ qS (word e p n)+
      cond μ (word e p n) (fun x => word e p L (e^[n] x))-(n : ℝ)*rate μ e p)
      atTop (𝓝 (cond μ qS (word e p n))) := by
    simpa only [add_sub_cancel_right] using
      ((cond_future_tendsto μ e he p hp n).const_add (cond μ qS (word e p n))).sub_const ((n : ℝ)*rate μ e p)
  obtain ⟨L,hL⟩ := (ht.eventually (gt_mem_nhds hsmall)).exists
  let r : X → (Fin L → A) := fun x => word e p L (e^[n] x)
  have hr : Measurable r := (word_measurable e e.measurable p hp L).comp (e.measurable.iterate n)
  have hc : cond μ qS r<ε := (cond_future_zero_bound μ e he p qS hp hqS hqz n L).trans_lt hL
  obtain ⟨g,hg⟩ := exists_decoder_error_le_cond μ qS r hqS hr
  let G (v : ℕ → A) := g (fun i : Fin L => v (i.val+1))
  have hG : Measurable G := (measurable_of_countable g).comp
    (Measurable.of_eval (fun i : Fin L => measurable_pi_apply (i.val+1)))
  have hcancel (x : X) : e^[M] (e.symm^[M] x)=x :=
    (show Function.LeftInverse (e : X → X) e.symm from e.apply_symm_apply).iterate M x
  have hnM : M≤n := by dsimp [n]; omega
  have hrx (x : X) : r (e.symm^[M] x)=(fun i : Fin L => tailName e p m x (i.val+1)) := by
    funext i
    change p (e^[i.val] (e^[n] (e.symm^[M] x)))=p (e^[i.val+1+m] x)
    rw [forward_iterate_inverse_sub e hnM,←Function.iterate_add_apply]
    congr 2
    dsimp [n]
    omega
  have hset : {x | G (tailName e p m x)≠q x}=
      (e.symm^[M]) ⁻¹' {x | qS x≠g (r x)} := by
    ext x
    change g (fun i : Fin L => tailName e p m x (i.val+1))≠q x ↔
      q (e^[M] (e.symm^[M] x))≠g (r (e.symm^[M] x))
    rw [hcancel,hrx]
    exact ne_comm
  have hEm : MeasurableSet {x | qS x≠g (r x)} :=
    (measurableSet_eq_fun hqS ((measurable_of_countable g).comp hr)).compl
  refine ⟨G,hG,?_⟩
  rw [hset,((he.symm e).iterate M).measure_preimage hEm.nullMeasurableSet,
    ←ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top,ENNReal.toReal_ofReal hε.le]
  exact hg.trans_lt hc

theorem TailObservable.reverse (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (p : X → A) (q : X → B) (hp : Measurable p) (hq : Measurable q)
    (ht : TailObservable μ e p q) : TailObservable μ e.symm p q := by
  have hz := tailObservable_rate_zero μ e he p hp q hq ht
  apply zero_entropy_opposite_factor μ e.symm (he.symm e) p q hp hq
  · simpa only [rate_inverse μ e he q hq] using hz
  · simpa only [MeasurableEquiv.symm_symm] using ht 0

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
variable {μ : Measure X} {T : X → X} {α : X → A} {E F : Set X}

lemma TailEvent.congr (hE : TailEvent μ T α E) (hEF : E=ᵐ[μ]F) : TailEvent μ T α F := by
  intro m
  obtain ⟨D,hD,he⟩ := hE m
  exact ⟨D,hD,hEF.symm.trans he⟩

lemma TailEvent.nullMeasurable (hT : Measurable T) (hα : Measurable α)
    (hE : TailEvent μ T α E) : NullMeasurableSet E μ := by
  obtain ⟨D,hD,he⟩ := hE 0
  exact (hD.preimage (measurable_tailName hT hα 0)).nullMeasurableSet.congr he.symm

lemma TailEvent.univ : TailEvent μ T α (Set.univ : Set X) := by
  intro m
  exact ⟨Set.univ,MeasurableSet.univ,by simp⟩

lemma TailEvent.compl (hE : TailEvent μ T α E) : TailEvent μ T α Eᶜ := by
  intro m
  obtain ⟨D,hD,he⟩ := hE m
  refine ⟨Dᶜ,hD.compl,?_⟩
  filter_upwards [he] with x hx
  exact congrArg Not hx

lemma TailEvent.iInter {I : Type*} [Countable I] {E : I → Set X}
    (hE : ∀ i,TailEvent μ T α (E i)) : TailEvent μ T α (⋂ i,E i) := by
  intro m
  choose D hD he using fun i => hE i m
  refine ⟨⋂ i,D i,MeasurableSet.iInter hD,?_⟩
  filter_upwards [ae_all_iff.mpr he] with x hx
  change (x∈⋂ i,E i)=(tailName T α m x∈⋂ i,D i)
  exact propext (by simp only [mem_iInter]; exact forall_congr' (fun i => Iff.of_eq (hx i)))

lemma TailEvent.inter (hE : TailEvent μ T α E) (hF : TailEvent μ T α F) :
    TailEvent μ T α (E∩F) := by
  intro m
  obtain ⟨D,hD,he⟩ := hE m
  obtain ⟨C,hC,hf⟩ := hF m
  refine ⟨D∩C,hD.inter hC,?_⟩
  filter_upwards [he,hf] with x hx hy
  exact congrArg₂ And hx hy

lemma TailEvent.preimage (hT : MeasurePreserving T μ μ) (hE : TailEvent μ T α E) :
    TailEvent μ T α (T ⁻¹' E) := by
  intro m
  obtain ⟨D,hD,he⟩ := hE m
  let σ (v : ℕ → A) (n : ℕ) := v (n+1)
  refine ⟨σ ⁻¹' D,hD.preimage (Measurable.of_eval (fun n => measurable_pi_apply (n+1))),?_⟩
  filter_upwards [hT.quasiMeasurePreserving.ae he] with x hx
  change (T x∈E)=(σ (tailName T α m x)∈D)
  change (T x∈E)=(tailName T α m (T x)∈D) at hx
  rw [hx]
  congr 1
  funext n
  simp only [tailName,σ,←Function.iterate_succ_apply]
  congr 2
  omega

lemma TailEvent.inverse_preimage (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (hE : TailEvent μ e α E) : TailEvent μ e α (e.symm ⁻¹' E) := by
  intro m
  obtain ⟨D,hD,h⟩ := hE (m+1)
  refine ⟨D,hD,?_⟩
  filter_upwards [(he.symm e).quasiMeasurePreserving.ae h] with x hx
  change (e.symm x∈E)=(tailName e α m x∈D)
  change (e.symm x∈E)=(tailName e α (m+1) (e.symm x)∈D) at hx
  rw [hx]
  congr 1
  funext n
  change α (e^[n+(m+1)] (e.symm x))=α (e^[n+m] x)
  rw [show n+(m+1)=(n+m)+1 by omega,Function.iterate_succ_apply,e.apply_symm_apply]

lemma TailEvent.reverse [IsProbabilityMeasure μ] [Fintype A] [MeasurableSingletonClass A]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) (hα : Measurable α)
    (hE : TailEvent μ e α E) : TailEvent μ e.symm α E := by
  classical
  obtain ⟨D,hD,hED⟩ := hE 0
  let F := tailName e α 0 ⁻¹' D
  have hF : MeasurableSet F := hD.preimage (measurable_tailName e.measurable hα 0)
  have hq : Measurable (fun x => decide (x∈F)) := by
    have hf : Measurable (fun x => if x∈F then (true : Bool) else false) := Measurable.ite hF measurable_const measurable_const
    convert hf using 1
    funext x
    by_cases hx : x∈F <;> simp [hx]
  have ht := (tailEvent_bool (hE.congr hED)).reverse μ e he α _ hα hq
  intro m
  obtain ⟨G,hG,hqG⟩ := ht m
  refine ⟨G ⁻¹' {true},hG (measurableSet_singleton true),?_⟩
  filter_upwards [hED,hqG] with x hx hy
  change (x∈E)=(G (tailName e.symm α m x)=true)
  change (x∈E)=(x∈F) at hx
  rw [hx]
  simpa only [Function.comp_def,decide_eq_true_eq] using congrArg (· = true) hy

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter
open scoped ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
variable {μ : Measure X} [IsFiniteMeasure μ] {T : X → X} {α : X → A}

def IsTailAtom (μ : Measure X) (T : X → X) (α : X → A) (C : Set X) : Prop :=
  TailEvent μ T α C ∧ 0<μ C ∧ ∀ E,TailEvent μ T α E → C ≤ᵐ[μ] E ∨ C ≤ᵐ[μ] Eᶜ

theorem exists_tailAtom_of_local_constancy (hT : Measurable T) (hα : Measurable α)
    {H : Set X} (hHp : 0<μ H)
    (hc : ∀ E,TailEvent μ T α E → H ≤ᵐ[μ] E ∨ H ≤ᵐ[μ] Eᶜ) :
    ∃ C : Set X,IsTailAtom μ T α C := by
  classical
  let S : Set ℝ≥0∞ := {r | ∃ E : Set X,TailEvent μ T α E ∧ H ≤ᵐ[μ] E ∧ μ E=r}
  have hS : S.Nonempty := ⟨μ univ,univ,TailEvent.univ,ae_of_all _ (fun x _ => @Set.mem_univ X x),rfl⟩
  obtain ⟨u,_,hu,hun⟩ := exists_seq_tendsto_sInf hS (OrderBot.bddBelow S)
  choose C hCt hHC hμC using hun
  let D : Set X := ⋂ n : ℕ,C n
  have hDt : TailEvent μ T α D := TailEvent.iInter hCt
  have hHD : H ≤ᵐ[μ] D := by
    filter_upwards [ae_all_iff.mpr hHC] with x hx hH
    exact mem_iInter.mpr (fun n => hx n hH)
  have hDmin : ∀ E,TailEvent μ T α E → H ≤ᵐ[μ] E → μ D≤μ E := by
    intro E ht hHE
    have hi : μ D ≤ sInf S := ge_of_tendsto hu (Eventually.of_forall (fun n => by
      rw [←hμC n]
      exact measure_mono (iInter_subset C n)))
    exact hi.trans (sInf_le (show μ E∈S from ⟨E,ht,hHE,rfl⟩))
  have hDp : 0<μ D := hHp.trans_le (measure_mono_ae hHD)
  refine ⟨D,hDt,hDp,?_⟩
  intro E hE
  have hmem (F : Set X) (hF : TailEvent μ T α F) (hHF : H ≤ᵐ[μ] F) : D ≤ᵐ[μ] F := by
    have hsub : (D∩F : Set X) ≤ᵐ[μ] D := ae_of_all _ (fun _ hx => hx.1)
    have hHDF : H ≤ᵐ[μ] (D∩F : Set X) := by
      filter_upwards [hHD,hHF] with x hx hy hz
      exact ⟨hx hz,hy hz⟩
    have he := ae_eq_of_ae_subset_of_measure_ge hsub (hDmin _ (hDt.inter hF) hHDF)
      ((hDt.inter hF).nullMeasurable hT hα) (measure_ne_top μ D)
    filter_upwards [he] with x hx hD
    exact ((Iff.of_eq hx).mpr hD).2
  rcases hc E hE with he|he
  · exact Or.inl (hmem E hE he)
  · exact Or.inr (hmem Eᶜ hE.compl he)

theorem tail_trivial_of_atom (hT : MeasurePreserving T μ μ) (hα : Measurable α)
    (herg : ∀ n : ℕ,0<n → Ergodic (T^[n]) μ)
    {C : Set X} (hC : IsTailAtom μ T α C) :
    ∀ E,TailEvent μ T α E → (∀ᵐ x ∂μ,x∈E) ∨ (∀ᵐ x ∂μ,x∉E) := by
  have hCm := hC.1.nullMeasurable hT.measurable hα
  obtain ⟨n,hn,hi⟩ := hT.conservative.exists_gt_measure_inter_ne_zero hCm hC.2.1.ne' 0
  have hpre : TailEvent μ T α (T^[n] ⁻¹' C) := by
    clear hn hi
    induction n with
    | zero => simpa using hC.1
    | succ n ih =>
      convert ih.preimage hT using 1
      ext x
      simp only [mem_preimage,Function.iterate_succ_apply]
  have hsub : C ≤ᵐ[μ] (T^[n] ⁻¹' C) := by
    rcases hC.2.2 _ hpre with hh|hh
    · exact hh
    · have hz : μ (C∩T^[n] ⁻¹' C)=0 := by
        apply measure_mono_null_ae (t := (∅ : Set X)) _ (measure_empty)
        filter_upwards [hh] with x hx hy
        exact (hx hy.1 hy.2).elim
      exact (hi hz).elim
  have heq := ae_eq_of_ae_subset_of_measure_ge hsub
    ((hT.iterate n).measure_preimage hCm).le hCm (measure_ne_top μ _)
  have hfull : ∀ᵐ x ∂μ,x∈C := by
    rcases (herg n hn).quasiErgodic.ae_mem_or_ae_notMem₀ hCm heq.symm with hh|hh
    · exact hh
    · have hz : μ C=0 := by simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hh
      exact (hC.2.1.ne' hz).elim
  intro E hE
  rcases hC.2.2 E hE with hh|hh
  · exact Or.inl (hfull.mp hh)
  · exact Or.inr (hfull.mp hh)

end HyperbolicCoding

end
section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology ENNReal symmDiff

namespace HyperbolicCoding

lemma law_distance_le_disagreement {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (κ : Measure Ω) [IsFiniteMeasure κ] {p q : Ω → Y}
    (hp : Measurable p) (hq : Measurable q) {D : Set Y} (hD : MeasurableSet D) :
    |(κ.map p).real D-(κ.map q).real D|≤κ.real {w | p w≠q w} := by
  simp only [Measure.real,Measure.map_apply hp hD,Measure.map_apply hq hD]
  apply (abs_measureReal_sub_le_measureReal_symmDiff
    (hD.preimage hp).nullMeasurableSet (hD.preimage hq).nullMeasurableSet).trans
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro w hw he
  have hh : (w∈p ⁻¹' D)=(w∈q ⁻¹' D) := by simp only [mem_preimage,he]
  simp only [Set.mem_symmDiff,hh,and_not_self,or_self] at hw

lemma tail_disagreement_tendsto_zero {Ω X A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace A] [MeasurableEq A]
    (κ : Measure Ω) [IsFiniteMeasure κ] {T : X → X} (hT : Measurable T)
    {α : X → A} (hα : Measurable α) {p q : Ω → X}
    (hp : Measurable p) (hq : Measurable q)
    (hname : ∀ᵐ w ∂κ,∀ᶠ n : ℕ in atTop,α (T^[n] (p w))=α (T^[n] (q w))) :
    Tendsto (fun m : ℕ => κ.real {w | tailName T α m (p w)≠tailName T α m (q w)})
      atTop (𝓝 0) := by
  let D (m : ℕ) : Set Ω := {w | tailName T α m (p w)≠tailName T α m (q w)}
  have hDm (m : ℕ) : MeasurableSet (D m) := by
    have he : {w | tailName T α m (p w)=tailName T α m (q w)}=
        ⋂ n : ℕ,{w | α (T^[n+m] (p w))=α (T^[n+m] (q w))} := by
      ext w
      simp only [mem_ofPred_eq,mem_iInter,funext_iff,tailName]
    change MeasurableSet ({w | tailName T α m (p w)=tailName T α m (q w)}ᶜ)
    rw [he]
    exact (MeasurableSet.iInter (fun n => measurableSet_eq_fun
      ((hα.comp (hT.iterate (n+m))).comp hp) ((hα.comp (hT.iterate (n+m))).comp hq))).compl
  have hDanti : Antitone D := by
    intro m n hmn w hw hwm
    apply hw
    funext i
    have hi := congrFun hwm (i+n-m)
    simpa only [tailName,show i+n-m+m=i+n from by omega] using hi
  have hi : κ (⋂ m,D m)=0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hname] with w hw hmem
    obtain ⟨m,hm⟩ := eventually_atTop.mp hw
    apply (mem_iInter.mp hmem m)
    funext i
    exact hm (i+m) (by omega)
  have h := tendsto_measure_iInter_atTop (μ := κ) (fun m => (hDm m).nullMeasurableSet)
    hDanti ⟨0,measure_ne_top _ _⟩
  rw [hi] at h
  have ht := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞)≠⊤)).comp h
  simpa only [Function.comp_def,ENNReal.toReal_zero,Measure.real,D] using ht

theorem product_remote_tail_independence {A B X C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace X]
    [MeasurableSpace C] [MeasurableEq C]
    (ν : Measure A) (η : Measure B) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    {π : A×B → X} (hπ : Measurable π) {S : X → X} (hS : Measurable S)
    {α : X → C} (hα : Measurable α)
    (hname : ∀ᵐ w : (A×B)×A ∂(ν.prod η).prod ν,∀ᶠ n : ℕ in atTop,
      α (S^[n] (π w.1))=α (S^[n] (π (w.2,w.1.2)))) :
    ∃ δ : ℕ → ℝ,Tendsto δ atTop (𝓝 0) ∧ (∀ m,0≤δ m) ∧ ∀ m : ℕ,
      ∀ D : Set (A×(ℕ → C)),MeasurableSet D →
      |((ν.prod η).map (fun p => (p.1,tailName S α m (π p)))).real D-
        (ν.prod ((ν.prod η).map (fun p => tailName S α m (π p)))).real D|≤δ m := by
  let κ := (ν.prod η).prod ν
  let p : (A×B)×A → X := fun w => π w.1
  let q : (A×B)×A → X := fun w => π (w.2,w.1.2)
  have hp : Measurable p := hπ.comp measurable_fst
  have hq : Measurable q := hπ.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  let δ (m : ℕ) : ℝ := κ.real {w | tailName S α m (p w)≠tailName S α m (q w)}
  refine ⟨δ,tail_disagreement_tendsto_zero κ hS hα hp hq hname,fun _ => ENNReal.toReal_nonneg,?_⟩
  intro m D hD
  let β : A×B → (ℕ → C) := fun p => tailName S α m (π p)
  have hβ : Measurable β := (measurable_tailName hS hα m).comp hπ
  let P : (A×B)×A → A×(ℕ → C) := fun w => (w.1.1,β w.1)
  let Q : (A×B)×A → A×(ℕ → C) := fun w => (w.1.1,β (w.2,w.1.2))
  have hP : Measurable P := (measurable_fst.comp measurable_fst).prodMk (hβ.comp measurable_fst)
  have hQ : Measurable Q := (measurable_fst.comp measurable_fst).prodMk
    (hβ.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
  have hmapP : κ.map P=(ν.prod η).map (fun p => (p.1,β p)) := by
    have hfst : MeasurePreserving (Prod.fst : (A×B)×A → A×B) κ (ν.prod η) := measurePreserving_fst
    rw [←hfst.map_eq,Measure.map_map (measurable_fst.prodMk hβ) measurable_fst]
    rfl
  have harr : MeasurePreserving (fun w : (A×B)×A => (w.1.1,(w.2,w.1.2))) κ (ν.prod (ν.prod η)) :=
    ((MeasurePreserving.id ν).prod (measurePreserving_swap (μ := η) (ν := ν))).comp
      (measurePreserving_prodAssoc ν η ν)
  have hmapQ : κ.map Q=ν.prod ((ν.prod η).map β) := by
    calc
      κ.map Q=(ν.prod (ν.prod η)).map (Prod.map id β) := by
        rw [←harr.map_eq,Measure.map_map (measurable_id.prodMap hβ) harr.measurable]
        rfl
      _=(ν.map id).prod ((ν.prod η).map β) :=
        (Measure.map_prod_map ν (ν.prod η) measurable_id hβ).symm
      _=_ := by rw [Measure.map_id]
  have hd := law_distance_le_disagreement κ hP hQ hD
  rw [hmapP,hmapQ] at hd
  simpa only [P,Q,p,q,β,δ,ne_eq,Prod.mk.injEq,true_and,not_true_eq_false] using hd

end HyperbolicCoding

end
section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal

namespace HyperbolicCoding

lemma map_withDensity_comp {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (κ : Measure Ω) {π : Ω → X} (hπ : Measurable π) {w : X → ℝ≥0∞} (hw : Measurable w) :
    (κ.withDensity (w ∘ π)).map π=(κ.map π).withDensity w := by
  ext D hD
  rw [Measure.map_apply hπ hD,withDensity_apply _ (hD.preimage hπ),
    withDensity_apply _ hD]
  exact (setLIntegral_map hD hw hπ).symm

theorem exists_exact_density_lift {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (κ : Measure Ω) (μ : Measure X) [IsProbabilityMeasure κ] [IsFiniteMeasure μ]
    {π : Ω → X} (hπ : Measurable π) (hac : κ.map π≪μ) :
    ∃ H : Set X,MeasurableSet H ∧ 0<μ H ∧
      ∃ w : Ω → ℝ≥0∞,Measurable w ∧
        MeasurePreserving π (κ.withDensity w) ((μ H)⁻¹ • μ.restrict H) ∧
        IsProbabilityMeasure (κ.withDensity w) ∧ κ.withDensity w≪κ := by
  let η := κ.map π
  have : IsProbabilityMeasure η := inferInstance
  let H : Set X := {x | η.rnDeriv μ x≠0}
  have hH : MeasurableSet H := (measurableSet_eq_fun (measurable_rnDeriv η μ) measurable_const).compl
  have hηH : η H=1 := by
    have hh : ∀ᵐ x ∂η,x∈H := (rnDeriv_pos hac).mono (fun _ hx => hx.ne')
    rw [← measure_univ (μ := η)]
    apply measure_congr
    filter_upwards [hh] with x hx
    exact propext (by simp only [mem_univ,iff_true]; exact hx)
  have hp : 0<μ H := by
    apply pos_iff_ne_zero.mpr
    intro hh
    have hz := hac hh
    rw [hηH] at hz
    exact one_ne_zero hz
  have hres : μ.restrict H≪η := by
    have hh : μ.restrict H≪(μ.restrict H).withDensity (η.rnDeriv μ) :=
      withDensity_absolutelyContinuous' (measurable_rnDeriv η μ).aemeasurable
        (by filter_upwards [ae_restrict_mem hH] with x hx; exact hx)
    rw [← restrict_withDensity hH,withDensity_rnDeriv_eq η μ hac] at hh
    exact hh.trans Measure.absolutelyContinuous_restrict
  let σ := (μ H)⁻¹ • μ.restrict H
  have hσ : σ≪η := smul_absolutelyContinuous.trans hres
  have : IsProbabilityMeasure σ := by
    constructor
    simp only [σ,Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul]
    exact ENNReal.inv_mul_cancel hp.ne' (measure_ne_top μ H)
  let w := σ.rnDeriv η ∘ π
  have hw : Measurable w := (measurable_rnDeriv σ η).comp hπ
  have hm : MeasurePreserving π (κ.withDensity w) σ := by
    refine ⟨hπ,?_⟩
    rw [show w=σ.rnDeriv η ∘ π from rfl,map_withDensity_comp κ hπ (measurable_rnDeriv σ η)]
    exact withDensity_rnDeriv_eq σ η hσ
  have hprob : IsProbabilityMeasure (κ.withDensity w) := by
    constructor
    have hu := congrArg (fun ν : Measure X => ν univ) hm.map_eq
    rw [Measure.map_apply hπ MeasurableSet.univ,preimage_univ,show σ univ=1 from measure_univ] at hu
    exact hu
  exact ⟨H,hH,hp,w,hw,hm,hprob,withDensity_absolutelyContinuous κ w⟩

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology
variable {X Ω A : Type*} [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace A]
variable [Fintype A] [MeasurableSingletonClass A]

theorem tailAtom_of_rectangle (μ : Measure X) (κ : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure κ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (α : X → A) (hα : Measurable α) {π : Ω → X}
    (hπ : QuasiMeasurePreserving π κ μ)
    (hc : ∀ E : Set X,TailEvent μ e α E → TailEvent μ e.symm α E →
      ∃ c : Prop,∀ᵐ p ∂κ,(π p∈E ↔ c)) :
    ∃ C : Set X,IsTailAtom μ e α C := by
  obtain ⟨H,hH,hHp,w,_,hm,_,hac⟩ := exists_exact_density_lift κ μ hπ.measurable hπ.absolutelyContinuous
  apply exists_tailAtom_of_local_constancy e.measurable hα hHp
  intro E hE
  obtain ⟨D,hD,heD⟩ := hE 0
  let F := tailName e α 0 ⁻¹' D
  have hF : MeasurableSet F := hD.preimage (measurable_tailName e.measurable hα 0)
  have hFt : TailEvent μ e α F := hE.congr heD
  obtain ⟨c,hc⟩ := hc F hFt (hFt.reverse e he hα)
  have hconst : ∀ᵐ p ∂κ.withDensity w,(π p∈F ↔ c) := hac.ae_le hc
  have hnorm : ∀ {p : X → Prop},(∀ᵐ x ∂((μ H)⁻¹ • μ.restrict H),p x) →
      ∀ᵐ x ∂μ,x∈H → p x := fun hh =>
    (ae_restrict_iff' hH).mp ((ae_ennreal_smul_measure_iff (ENNReal.inv_ne_zero.mpr (measure_ne_top μ H))).mp hh)
  by_cases hc : c
  · have hh : ∀ᵐ p ∂κ.withDensity w,π p∈F := hconst.mono (fun _ hp => hp.mpr hc)
    have hf : ∀ᵐ x ∂((μ H)⁻¹ • μ.restrict H),x∈F := by
      rw [←hm.map_eq]
      exact (ae_map_iff hm.measurable.aemeasurable hF).mpr hh
    refine Or.inl ?_
    filter_upwards [hnorm hf,heD] with x hx hy hz
    exact (Iff.of_eq hy).mpr (hx hz)
  · have hh : ∀ᵐ p ∂κ.withDensity w,π p∉F := hconst.mono (fun _ hp hf => hc (hp.mp hf))
    have hf : ∀ᵐ x ∂((μ H)⁻¹ • μ.restrict H),x∉F := by
      rw [←hm.map_eq]
      exact (ae_map_iff hm.measurable.aemeasurable hF.compl).mpr hh
    refine Or.inr ?_
    filter_upwards [hnorm hf,heD] with x hx hy hz hE
    exact hx hz ((Iff.of_eq hy).mp hE)

end HyperbolicCoding

end
end

end OAI
