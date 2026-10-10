import OAI.InformationTheory.Entanglement.IndependentTapes

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Function
open scoped MeasureTheory ProbabilityTheory unitInterval
namespace SecretKey
variable {Ω S X : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
  [MeasurableSpace X]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem sampled_pair_law (H : Ω → S) (U : Ω → I)
    (hH : Measurable H) (hU : Measurable U) (hind : IndepFun H U μ)
    (hUlaw : μ.map U=volume) (κ : Kernel S X) [IsMarkovKernel κ]
    (f : S → I → X) (hf : Measurable (uncurry f))
    (hmap : ∀ s, volume.map (f s)=κ s) :
    μ.map (fun ω => (H ω,f (H ω) (U ω)))=μ.map H ⊗ₘ κ := by
  let g : S×I → S×X := fun p => (p.1,f p.1 p.2)
  have hg : Measurable g := measurable_fst.prodMk hf
  have he : μ.map (fun ω => (H ω,f (H ω) (U ω)))=
      ((μ.map H).prod volume).map g := by
    rw [← hUlaw,← hind.map_prod_eq_prod_map_map hH.aemeasurable hU.aemeasurable,
      Measure.map_map hg (hH.prodMk hU)]
    rfl
  rw [he]
  ext E hE
  rw [Measure.map_apply hg hE,Measure.prod_apply (hg hE),Measure.compProd_apply hE]
  apply lintegral_congr
  intro s
  have hm : Measurable (f s) := hf.comp (measurable_const.prodMk measurable_id)
  rw [← hmap s,Measure.map_apply hm (measurable_prodMk_left hE)]
  rfl

variable (f : (k : ℕ) → (Fin k → X) → I → X)

def sampledPrefix : (k : ℕ) → UniformTapes ℕ → (Fin k → X)
  | 0,_ => Fin.elim0
  | k+1,ω => Fin.snoc (sampledPrefix k ω) (f k (sampledPrefix k ω) (ω k))
def sampledHistory (ω : UniformTapes ℕ) (k : ℕ) : X :=
  f k (sampledPrefix f k ω) (ω k)
omit [MeasurableSpace X] in
lemma sampledPrefix_succ (k : ℕ) (ω : UniformTapes ℕ) :
    sampledPrefix f (k+1) ω=Fin.snoc (sampledPrefix f k ω) (sampledHistory f ω k) := rfl
omit [MeasurableSpace X] in
lemma sampledPrefix_eq (k : ℕ) (ω : UniformTapes ℕ) (i : Fin k) :
    sampledPrefix f k ω i=sampledHistory f ω i := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [sampledPrefix_succ,Fin.snoc_last,Fin.val_last]
    · simpa only [sampledPrefix_succ,Fin.snoc_castSucc,Fin.val_castSucc] using ih j

lemma measurable_tape_coordinate (s : Set ℕ) (k : ℕ) (hk : k∈s) :
    Measurable[tapeInformation s] (fun ω : UniformTapes ℕ => ω k) := by
  rw [measurable_iff_comap_le]
  exact le_iSup_of_le k (le_iSup_of_le hk le_rfl)
lemma sampledPrefix_measurable (hf : ∀ k, Measurable (uncurry (f k))) (k : ℕ) :
    Measurable[tapeInformation (Set.Iio k)] (sampledPrefix f k) := by
  induction k with
  | zero =>
    let : MeasurableSpace (UniformTapes ℕ) := tapeInformation (Set.Iio 0)
    apply Measurable.of_eval; intro i; exact Fin.elim0 i
  | succ k ih =>
    let : MeasurableSpace (UniformTapes ℕ) := tapeInformation (Set.Iio (k+1))
    have hp : Measurable[tapeInformation (Set.Iio (k+1))] (sampledPrefix f k) :=
      ih.mono (tapeInformation_mono (fun _ h => Nat.lt_trans h (Nat.lt_succ_self k))) le_rfl
    have hu := measurable_tape_coordinate (Set.Iio (k+1)) k (Nat.lt_succ_self k)
    apply Measurable.of_eval
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [sampledPrefix_succ,sampledHistory,Fin.snoc_last,Function.comp_def,Function.uncurry] using (hf k).comp (hp.prodMk hu)
    · simpa only [sampledPrefix_succ,Fin.snoc_castSucc,Function.comp_def] using (measurable_pi_apply j).comp hp
lemma sampledPrefix_measurable_global (hf : ∀ k, Measurable (uncurry (f k))) (k : ℕ) :
    Measurable (sampledPrefix f k) :=
  (sampledPrefix_measurable f hf k).mono (tapeInformation_le _) le_rfl
lemma sampledHistory_measurable (hf : ∀ k, Measurable (uncurry (f k))) :
    Measurable (sampledHistory f) := by
  apply Measurable.of_eval
  intro k
  exact (hf k).comp ((sampledPrefix_measurable_global f hf k).prodMk (measurable_pi_apply k))

theorem sampled_history_step (hf : ∀ k, Measurable (uncurry (f k)))
    (κ : (k : ℕ) → Kernel (Fin k → X) X) [∀ k, IsMarkovKernel (κ k)]
    (hmap : ∀ k s, volume.map (f k s)=κ k s) (k : ℕ) :
    uniformTapesLaw.map (fun ω => (sampledPrefix f k ω,sampledHistory f ω k))=
      uniformTapesLaw.map (sampledPrefix f k) ⊗ₘ κ k := by
  apply sampled_pair_law _ _ (sampledPrefix_measurable_global f hf k)
    (measurable_pi_apply k) _ (tape_coordinate_law k) (κ k) (f k) (hf k) (hmap k)
  exact fresh_coordinate_independent (by simp only [Set.mem_Iio]; exact lt_irrefl k) _
    (sampledPrefix_measurable f hf k)

end SecretKey

namespace SecretKey
open MeasureTheory ProbabilityTheory Function
open scoped MeasureTheory ProbabilityTheory unitInterval
variable {X : Type*} [MeasurableSpace X]
def recordPrefix (k : ℕ) (x : ℕ → X) : Fin k → X := fun i => x i
lemma recordPrefix_measurable (k : ℕ) : Measurable (recordPrefix (X := X) k) := by
  apply Measurable.of_eval; intro i; exact measurable_pi_apply i.val
lemma snoc_measurable (k : ℕ) :
    Measurable (fun p : (Fin k → X)×X => Fin.snoc (α := fun _ : Fin (k+1) => X) p.1 p.2) := by
  apply Measurable.of_eval
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.snoc_last] using measurable_snd
  · simpa only [Fin.snoc_castSucc,Function.comp_def] using (measurable_pi_apply j).comp measurable_fst
omit [MeasurableSpace X] in
lemma recordPrefix_succ (k : ℕ) (x : ℕ → X) :
    recordPrefix (k+1) x=Fin.snoc (recordPrefix k x) (x k) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [recordPrefix]

theorem full_history_law_unique (ν ξ : Measure (ℕ → X)) [IsFiniteMeasure ν]
    (h : ∀ k, ν.map (recordPrefix k)=ξ.map (recordPrefix k)) : ν=ξ := by
  let P := fun J : Finset ℕ => ν.map J.restrict
  have hν : IsProjectiveLimit ν P := fun J => rfl
  have hξ : IsProjectiveLimit ξ P := by
    intro J
    let k := J.sup id+1
    have hb (i : J) : i.val<k := Nat.lt_succ_of_le (Finset.le_sup (f := id) i.property)
    let g : (Fin k → X) → (J → X) := fun x i => x ⟨i.val,hb i⟩
    have hg : Measurable g := by fun_prop
    have he : J.restrict=(g ∘ recordPrefix k : (ℕ → X) → (J → X)) := rfl
    change ξ.map J.restrict=ν.map J.restrict
    rw [he,← Measure.map_map hg (recordPrefix_measurable k),
      ← Measure.map_map hg (recordPrefix_measurable k),h k]
  exact hν.unique hξ

theorem sampled_full_history_law
    (f : (k : ℕ) → (Fin k → X) → I → X)
    (hf : ∀ k, Measurable (uncurry (f k)))
    (κ : (k : ℕ) → Kernel (Fin k → X) X) [∀ k, IsMarkovKernel (κ k)]
    (hmap : ∀ k s, volume.map (f k s)=κ k s)
    (ν : Measure (ℕ → X)) [IsProbabilityMeasure ν]
    (hν : ∀ k, ν.map (fun x => (recordPrefix k x,x k))=ν.map (recordPrefix k) ⊗ₘ κ k) :
    ν=uniformTapesLaw.map (sampledHistory f) := by
  have hp : ∀ k, ν.map (recordPrefix k)=uniformTapesLaw.map (sampledPrefix f k) := by
    intro k
    induction k with
    | zero =>
      have he : recordPrefix (X := X) 0=(fun _ : ℕ → X => (Fin.elim0 : Fin 0 → X)) := by
        funext x i; exact Fin.elim0 i
      have hf0 : sampledPrefix f 0=(fun _ : UniformTapes ℕ => (Fin.elim0 : Fin 0 → X)) := rfl
      rw [he,hf0,Measure.map_const,Measure.map_const]
      simp
    | succ k ih =>
      have he : recordPrefix (X := X) (k+1)=
          (fun p : (Fin k → X)×X => Fin.snoc (α := fun _ : Fin (k+1) => X) p.1 p.2) ∘ (fun x => (recordPrefix k x,x k)) := by
        funext x; exact recordPrefix_succ k x
      have hx : Measurable (fun ω : UniformTapes ℕ => sampledHistory f ω k) := by
        simpa only [Function.comp_def] using
          (measurable_pi_apply k).comp (sampledHistory_measurable f hf)
      rw [he,← Measure.map_map (snoc_measurable k)
        ((recordPrefix_measurable k).prodMk (measurable_pi_apply k)),hν k,ih,
        ← sampled_history_step f hf κ hmap k,Measure.map_map (snoc_measurable k)
          ((sampledPrefix_measurable_global f hf k).prodMk hx)]
      rfl
  apply full_history_law_unique
  intro k
  rw [Measure.map_map (recordPrefix_measurable k) (sampledHistory_measurable f hf),hp k]
  congr 1
  funext ω i
  exact sampledPrefix_eq f k ω i

end SecretKey

end

end OAI
