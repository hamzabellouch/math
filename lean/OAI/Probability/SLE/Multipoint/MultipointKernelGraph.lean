import OAI.Probability.SLE.Multipoint.MultipointDistanceKernel

namespace OAI

/-! The finite graph elimination used in the capped distance kernel.
An edge records one selected inverse-distance factor. Each vertex has
at most one outgoing edge, including after deleting a vertex. -/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace SLEExactGauge.Multipoint

def incidentEdges {ι : Type*} [DecidableEq ι] (E : Finset (ι × ι)) (v : ι) : Finset (ι × ι) :=
  E.filter (fun e => e.1=v ∨ e.2=v)

def eraseVertex {ι : Type*} [DecidableEq ι] (E : Finset (ι × ι)) (v : ι) : Finset (ι × ι) :=
  E.filter (fun e => e.1≠v ∧ e.2≠v)

def graphKernel {ι : Type*} (α : ℝ) (E : Finset (ι × ι)) (x : ι → ℂ) : ℝ≥0∞ :=
  ∏ e ∈ E, distanceKernel α (x e.1) (x e.2)

lemma measurable_graphKernel {ι : Type*} (α : ℝ) (E : Finset (ι × ι)) :
    Measurable (graphKernel α E) := by
  unfold graphKernel distanceKernel
  fun_prop

lemma exists_vertex_incident_card_le_two {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (hS : S.Nonempty) (E : Finset (ι × ι))
    (hends : ∀ e ∈ E, e.1 ∈ S ∧ e.2 ∈ S)
    (hout : ∀ e ∈ E, ∀ f ∈ E, e.1=f.1 → e=f) :
    ∃ v ∈ S, (incidentEdges E v).card ≤ 2 := by
  have hcard : E.card ≤ S.card :=
    Finset.card_le_card_of_injOn Prod.fst (fun e he => (hends e he).1)
      (fun e he f hf hef => hout e he f hf hef)
  have hsum : E.card = ∑ v ∈ S, (E.filter (fun e => e.2=v)).card :=
    Finset.card_eq_sum_card_fiberwise (fun e he => (hends e he).2)
  have hin : ∃ v ∈ S, (E.filter (fun e => e.2=v)).card ≤ 1 := by
    by_contra! h
    have hlt : S.card < ∑ v ∈ S, (E.filter (fun e => e.2=v)).card := by
      calc
        S.card = ∑ _v ∈ S, 1 := by simp
        _ < _ := Finset.sum_lt_sum (fun v hv => (h v hv).le)
          (by obtain ⟨v,hv⟩ := hS; exact ⟨v,hv,h v hv⟩)
    omega
  obtain ⟨v,hv,hin⟩ := hin
  have houtcard : (E.filter (fun e => e.1=v)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro e he f hf
    exact hout e (Finset.mem_filter.mp he).1 f (Finset.mem_filter.mp hf).1
      ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm)
  have heq : incidentEdges E v = (E.filter (fun e => e.1=v)) ∪ (E.filter (fun e => e.2=v)) := by
    ext e
    simp only [incidentEdges,Finset.mem_filter,Finset.mem_union]
    tauto
  refine ⟨v,hv,?_⟩
  rw [heq]
  exact (Finset.card_union_le _ _).trans (by omega)

lemma incoming_card_le_erase {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (E : Finset (ι × ι)) (v : ι)
    (hends : ∀ e ∈ E, e.1 ∈ S ∧ e.2 ∈ S)
    (hout : ∀ e ∈ E, ∀ f ∈ E, e.1=f.1 → e=f)
    (hloop : ∀ e ∈ E, e.1≠e.2) :
    (E.filter (fun e => e.2=v)).card ≤ (S.erase v).card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro e he
    obtain ⟨he,hev⟩ := Finset.mem_filter.mp he
    exact Finset.mem_erase.mpr ⟨by simpa only [← hev] using hloop e he,(hends e he).1⟩
  · intro e he f hf hef
    exact hout e (Finset.mem_filter.mp he).1 f (Finset.mem_filter.mp hf).1 hef

/-- The low-incidence vertex can be chosen among the integration
variables even when one additional vertex is fixed. -/
lemma exists_free_vertex_incident_card_le_two {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (hS : S.Nonempty) (root : ι) (hr : root ∉ S)
    (E : Finset (ι × ι))
    (hends : ∀ e ∈ E, e.1 ∈ insert root S ∧ e.2 ∈ insert root S)
    (hout : ∀ e ∈ E, ∀ f ∈ E, e.1=f.1 → e=f)
    (hloop : ∀ e ∈ E, e.1≠e.2) :
    ∃ v ∈ S, (incidentEdges E v).card ≤ 2 := by
  have hcard : E.card ≤ S.card+1 := by
    have hh := Finset.card_le_card_of_injOn Prod.fst (fun e he => (hends e he).1)
      (fun e he f hf hef => hout e he f hf hef)
    simpa only [Finset.card_insert_of_notMem hr] using hh
  have hsum : (∑ v ∈ S, (E.filter (fun e => e.2=v)).card) ≤ E.card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    exact Finset.card_filter_le _ _
  have hin : ∃ v ∈ S, (E.filter (fun e => e.2=v)).card ≤ 1 := by
    by_cases hS1 : S.card=1
    · obtain ⟨v,hv⟩ := hS
      refine ⟨v,hv,?_⟩
      have hh := incoming_card_le_erase (insert root S) E v hends hout hloop
      have hv' : v ∈ insert root S := Finset.mem_insert_of_mem hv
      simpa only [Finset.card_erase_of_mem hv',Finset.card_insert_of_notMem hr,hS1] using hh
    · by_contra! hn
      have htwo : S.card*2 ≤ ∑ v ∈ S, (E.filter (fun e => e.2=v)).card := by
        simpa only [Finset.sum_const,smul_eq_mul] using
          (Finset.sum_le_sum (s := S) (f := fun _ => (2 : ℕ))
            (g := fun v => (E.filter (fun e : ι × ι => e.2=v)).card)
            (fun v hv => Nat.succ_le_of_lt (hn v hv)))
      have hpos := Finset.card_pos.mpr hS
      omega
  obtain ⟨v,hv,hin⟩ := hin
  have houtcard : (E.filter (fun e => e.1=v)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro e he f hf
    exact hout e (Finset.mem_filter.mp he).1 f (Finset.mem_filter.mp hf).1
      ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm)
  have heq : incidentEdges E v = (E.filter (fun e => e.1=v)) ∪ (E.filter (fun e => e.2=v)) := by
    ext e
    simp only [incidentEdges,Finset.mem_filter,Finset.mem_union]
    tauto
  refine ⟨v,hv,?_⟩
  rw [heq]
  exact (Finset.card_union_le _ _).trans (by omega)

lemma eraseVertex_properties {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (E : Finset (ι × ι)) (v : ι)
    (hends : ∀ e ∈ E, e.1 ∈ S ∧ e.2 ∈ S)
    (hout : ∀ e ∈ E, ∀ f ∈ E, e.1=f.1 → e=f)
    (hloop : ∀ e ∈ E, e.1≠e.2) :
    (∀ e ∈ eraseVertex E v, e.1 ∈ S.erase v ∧ e.2 ∈ S.erase v) ∧
    (∀ e ∈ eraseVertex E v, ∀ f ∈ eraseVertex E v, e.1=f.1 → e=f) ∧
    (∀ e ∈ eraseVertex E v, e.1≠e.2) := by
  refine ⟨?_,?_,?_⟩
  · intro e he
    obtain ⟨he,h1,h2⟩ := Finset.mem_filter.mp he
    exact ⟨Finset.mem_erase.mpr ⟨h1,(hends e he).1⟩,
      Finset.mem_erase.mpr ⟨h2,(hends e he).2⟩⟩
  · intro e he f hf
    exact hout e (Finset.mem_filter.mp he).1 f (Finset.mem_filter.mp hf).1
  · intro e he
    exact hloop e (Finset.mem_filter.mp he).1

lemma graphKernel_split_vertex {ι : Type*} [DecidableEq ι]
    (α : ℝ) (E : Finset (ι × ι)) (v : ι) (x : ι → ℂ) :
    graphKernel α E x = graphKernel α (incidentEdges E v) x * graphKernel α (eraseVertex E v) x := by
  unfold graphKernel incidentEdges eraseVertex
  have he : E.filter (fun e => e.1≠v ∧ e.2≠v) = E.filter (fun e => ¬(e.1=v ∨ e.2=v)) := by
    ext e
    simp only [Finset.mem_filter,not_or]
  rw [he]
  exact (Finset.prod_filter_mul_prod_filter_not _ _ _).symm

lemma graphKernel_erase_update {ι : Type*} [DecidableEq ι]
    (α : ℝ) (E : Finset (ι × ι)) (v : ι) (x : ι → ℂ) (y : ℂ) :
    graphKernel α (eraseVertex E v) (Function.update x v y) = graphKernel α (eraseVertex E v) x := by
  apply Finset.prod_congr rfl
  intro e he
  obtain ⟨_,h1,h2⟩ := Finset.mem_filter.mp he
  simp only [Function.update_of_ne h1,Function.update_of_ne h2]

lemma incident_edge_section {ι : Type*} [DecidableEq ι]
    (α : ℝ) (e : ι × ι) (v : ι) (x : ι → ℂ)
    (hinc : e.1=v ∨ e.2=v) (hloop : e.1≠e.2) :
    ∃ c : ℂ, ∀ y, distanceKernel α ((Function.update x v y) e.1)
      ((Function.update x v y) e.2) = distanceKernel α y c := by
  rcases hinc with h1 | h2
  · have h2 : e.2≠v := by rw [← h1]; exact hloop.symm
    refine ⟨x e.2,fun y => ?_⟩
    rw [h1,Function.update_self,Function.update_of_ne h2]
  · have h1 : e.1≠v := by rw [← h2]; exact hloop
    refine ⟨x e.1,fun y => ?_⟩
    rw [h2,Function.update_self,Function.update_of_ne h1,distanceKernel_symm]

lemma incident_kernel_section_le {ι : Type*} [DecidableEq ι]
    (α : ℝ) (K : Set ℂ) (C : ℝ≥0∞)
    (hC0 : volume K ≤ C)
    (hC1 : ∀ y, (∫⁻ x in K, distanceKernel α x y) ≤ C)
    (hC2 : ∀ y z, (∫⁻ x in K, distanceKernel α x y * distanceKernel α x z) ≤ C)
    (E : Finset (ι × ι)) (v : ι) (x : ι → ℂ)
    (hcard : E.card ≤ 2) (hinc : ∀ e ∈ E, e.1=v ∨ e.2=v)
    (hloop : ∀ e ∈ E, e.1≠e.2) :
    (∫⁻ y in K, graphKernel α E (Function.update x v y)) ≤ C := by
  have hcases : E.card=0 ∨ E.card=1 ∨ E.card=2 := by omega
  rcases hcases with h0 | h1 | h2
  · have he : E=∅ := Finset.card_eq_zero.mp h0
    simpa only [he,graphKernel,Finset.prod_empty,lintegral_const,
      Measure.restrict_apply_univ,one_mul] using hC0
  · obtain ⟨e,he⟩ := Finset.card_eq_one.mp h1
    have hem : e ∈ E := he ▸ Finset.mem_singleton_self e
    obtain ⟨c,hc⟩ := incident_edge_section α e v x (hinc e hem) (hloop e hem)
    simpa only [he,graphKernel,Finset.prod_singleton,hc] using hC1 c
  · obtain ⟨e,f,hef,he⟩ := Finset.card_eq_two.mp h2
    have hem : e ∈ E := he ▸ Finset.mem_insert_self e {f}
    have hfm : f ∈ E := he ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self f)
    obtain ⟨c,hc⟩ := incident_edge_section α e v x (hinc e hem) (hloop e hem)
    obtain ⟨d,hd⟩ := incident_edge_section α f v x (hinc f hfm) (hloop f hfm)
    simpa only [he,graphKernel,Finset.prod_pair hef,hc,hd] using hC2 c d

lemma graphKernel_section_le {ι : Type*} [DecidableEq ι]
    (α : ℝ) (K : Set ℂ) (C : ℝ≥0∞)
    (hC0 : volume K ≤ C)
    (hC1 : ∀ y, (∫⁻ x in K, distanceKernel α x y) ≤ C)
    (hC2 : ∀ y z, (∫⁻ x in K, distanceKernel α x y * distanceKernel α x z) ≤ C)
    (E : Finset (ι × ι)) (v : ι) (x : ι → ℂ)
    (hcard : (incidentEdges E v).card ≤ 2) (hloop : ∀ e ∈ E, e.1≠e.2) :
    (∫⁻ y in K, graphKernel α E (Function.update x v y)) ≤
      C*graphKernel α (eraseVertex E v) x := by
  have he (y : ℂ) : graphKernel α E (Function.update x v y) =
      graphKernel α (incidentEdges E v) (Function.update x v y) *
        graphKernel α (eraseVertex E v) x := by
    rw [graphKernel_split_vertex α E v,graphKernel_erase_update]
  simp_rw [he]
  have hu : Measurable (fun y : ℂ => Function.update x v y) := by fun_prop
  have hm : Measurable (fun y : ℂ => graphKernel α (incidentEdges E v) (Function.update x v y)) :=
    (measurable_graphKernel α (incidentEdges E v)).comp hu
  rw [lintegral_mul_const _ hm]
  have hh := incident_kernel_section_le α K C hC0 hC1 hC2 (incidentEdges E v) v x hcard
    (fun e he => (Finset.mem_filter.mp he).2)
    (fun e he => hloop e (Finset.mem_filter.mp he).1)
  gcongr

theorem graphKernel_marginal_le_with_root {ι : Type*} [DecidableEq ι]
    (α : ℝ) (K : Set ℂ) (C : ℝ≥0∞) (hC : C < ⊤)
    (hC0 : volume K ≤ C)
    (hC1 : ∀ y, (∫⁻ x in K, distanceKernel α x y) ≤ C)
    (hC2 : ∀ y z, (∫⁻ x in K, distanceKernel α x y * distanceKernel α x z) ≤ C)
    (root : ι) (S : Finset ι) (E : Finset (ι × ι)) (hr : root ∉ S)
    (hends : ∀ e ∈ E, e.1 ∈ insert root S ∧ e.2 ∈ insert root S)
    (hout : ∀ e ∈ E, ∀ f ∈ E, e.1=f.1 → e=f)
    (hloop : ∀ e ∈ E, e.1≠e.2) (x : ι → ℂ) :
    lmarginal (fun _ : ι => volume.restrict K) S (graphKernel α E) x ≤ C^S.card := by
  induction S using Finset.strongInductionOn generalizing E with
  | _ S ih =>
    by_cases hempty : S=∅
    · have hE : E=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro e he
        have hs := hends e he
        simp only [hempty,Finset.mem_insert,Finset.notMem_empty,or_false] at hs
        exact hloop e he (hs.1.trans hs.2.symm)
      simp only [hempty,hE,lmarginal_empty,graphKernel,Finset.prod_empty,Finset.card_empty,pow_zero,le_rfl]
    · obtain ⟨v,hv,hdegree⟩ := exists_free_vertex_incident_card_le_two S
        (Finset.nonempty_iff_ne_empty.mpr hempty) root hr E hends hout hloop
      have hr' : root ∉ S.erase v := fun h => hr (Finset.mem_of_mem_erase h)
      have hends' : ∀ e ∈ eraseVertex E v,
          e.1 ∈ insert root (S.erase v) ∧ e.2 ∈ insert root (S.erase v) := by
        intro e he
        obtain ⟨he,h1,h2⟩ := Finset.mem_filter.mp he
        constructor
        · rcases Finset.mem_insert.mp (hends e he).1 with h | h
          · exact Finset.mem_insert.mpr (Or.inl h)
          · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨h1,h⟩))
        · rcases Finset.mem_insert.mp (hends e he).2 with h | h
          · exact Finset.mem_insert.mpr (Or.inl h)
          · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨h2,h⟩))
      have hout' : ∀ e ∈ eraseVertex E v, ∀ f ∈ eraseVertex E v, e.1=f.1 → e=f :=
        fun e he f hf => hout e (Finset.mem_filter.mp he).1 f (Finset.mem_filter.mp hf).1
      have hloop' : ∀ e ∈ eraseVertex E v, e.1≠e.2 :=
        fun e he => hloop e (Finset.mem_filter.mp he).1
      have hsmall := ih (S.erase v) (Finset.erase_ssubset hv) (eraseVertex E v) hr' hends' hout' hloop'
      calc
        lmarginal (fun _ : ι => volume.restrict K) S (graphKernel α E) x =
            lmarginal (fun _ : ι => volume.restrict K) (S.erase v)
              (fun x => ∫⁻ y in K, graphKernel α E (Function.update x v y)) x := by
          exact congrFun (lmarginal_erase' (μ := fun _ : ι => volume.restrict K)
            (graphKernel α E) (measurable_graphKernel α E) hv) x
        _ ≤ lmarginal (fun _ : ι => volume.restrict K) (S.erase v)
              (fun x => C*graphKernel α (eraseVertex E v) x) x :=
          lmarginal_mono (fun x => graphKernel_section_le α K C hC0 hC1 hC2 E v x hdegree hloop) x
        _ = C*lmarginal (fun _ : ι => volume.restrict K) (S.erase v)
              (graphKernel α (eraseVertex E v)) x := by
          exact lintegral_const_mul' C _ hC.ne
        _ ≤ C*C^(S.erase v).card := by gcongr
        _ = C^S.card := by
          rw [← Finset.card_erase_add_one hv,pow_succ,mul_comm]

end SLEExactGauge.Multipoint

end

end OAI
