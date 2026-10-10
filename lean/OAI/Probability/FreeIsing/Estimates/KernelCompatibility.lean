import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Problem367.KernelCompatibility

variable {P F X : Type*} [MeasurableSpace P] [MeasurableSpace F] [MeasurableSpace X]

theorem map_compProd_comap {W : Type*} [MeasurableSpace W]
    (mu : Measure W) [SFinite mu] (f : W → P) (hf : Measurable f)
    (kappa : Kernel P X) [IsSFiniteKernel kappa] :
    (mu ⊗ₘ kappa.comap f hf).map (Prod.map f id) = mu.map f ⊗ₘ kappa := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg (by fun_prop),
    Measure.lintegral_compProd (by fun_prop), Measure.lintegral_compProd hg,
    lintegral_map hg.lintegral_kernel_prod_right' hf]
  rfl

theorem map_compProd_of_kernel_map_ae {W O : Type*}
    [MeasurableSpace W] [MeasurableSpace O]
    (mu : Measure W) [SFinite mu] (f : W → P) (hf : Measurable f)
    (g : O → X) (hg : Measurable g)
    (eta : Kernel W O) [IsSFiniteKernel eta]
    (kappa : Kernel P X) [IsSFiniteKernel kappa]
    (h : (fun w => (eta.map g) w) =ᵐ[mu] (fun w => kappa (f w))) :
    (mu ⊗ₘ eta).map (Prod.map f g) = mu.map f ⊗ₘ kappa := by
  have h' : eta.map g =ᵐ[mu] kappa.comap f hf := h
  calc
    (mu ⊗ₘ eta).map (Prod.map f g) =
        (mu ⊗ₘ eta.map g).map (Prod.map f id) := by
      rw [Measure.compProd_map hg, Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = (mu ⊗ₘ kappa.comap f hf).map (Prod.map f id) := by
      rw [Measure.compProd_congr h']
    _ = mu.map f ⊗ₘ kappa := map_compProd_comap mu f hf kappa

theorem map_reorder_compProd (mu : Measure P) (nu : Measure F)
    [SFinite mu] [SFinite nu] (kappa : Kernel P X) [IsSFiniteKernel kappa] :
    ((mu.prod nu) ⊗ₘ kappa.comap Prod.fst measurable_fst).map
        (fun q : (P × F) × X => ((q.1.1, q.2), q.1.2)) =
      (mu ⊗ₘ kappa).prod nu := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (by fun_prop)]
  rw [Measure.lintegral_compProd (by fun_prop)]
  have hF : Measurable (fun q : (P × F) × X => f ((q.1.1, q.2), q.1.2)) :=
    hf.comp (by fun_prop)
  rw [lintegral_prod _ hF.lintegral_kernel_prod_right'.aemeasurable]
  rw [lintegral_prod _ hf.aemeasurable]
  rw [Measure.lintegral_compProd (by fun_prop)]
  apply lintegral_congr
  intro p
  simp only [Kernel.comap_apply]
  exact lintegral_lintegral_swap (by fun_prop)

theorem map_reorder_compProd_of_ae (mu : Measure P) (nu : Measure F)
    [SFinite mu] [SFinite nu] (kappa : Kernel P X) [IsSFiniteKernel kappa]
    (eta : Kernel (P × F) X) [IsSFiniteKernel eta]
    (h : (fun p : P × F => eta p) =ᵐ[mu.prod nu] (fun p => kappa p.1)) :
    ((mu.prod nu) ⊗ₘ eta).map
        (fun q : (P × F) × X => ((q.1.1, q.2), q.1.2)) =
      (mu ⊗ₘ kappa).prod nu := by
  have h' : eta =ᵐ[mu.prod nu]
      (kappa.comap Prod.fst measurable_fst : Kernel (P × F) X) := h
  rw [Measure.compProd_congr h']
  exact map_reorder_compProd mu nu kappa

theorem indepFun_future_of_past_kernel (mu : Measure P) (nu : Measure F)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (kappa : Kernel P X) [IsMarkovKernel kappa] :
    IndepFun (fun q : (P × F) × X => (q.1.1, q.2)) (fun q => q.1.2)
      ((mu.prod nu) ⊗ₘ kappa.comap Prod.fst measurable_fst) := by
  let rho := (mu.prod nu) ⊗ₘ kappa.comap Prod.fst measurable_fst
  have hr : rho.map (fun q : (P × F) × X => ((q.1.1, q.2), q.1.2)) =
      (mu ⊗ₘ kappa).prod nu := map_reorder_compProd mu nu kappa
  have hp : rho.map (fun q : (P × F) × X => (q.1.1, q.2)) = mu ⊗ₘ kappa := by
    have h := congrArg (fun m : Measure ((P × X) × F) => m.map Prod.fst) hr
    rw [Measure.map_map measurable_fst (by fun_prop)] at h
    simpa [Function.comp_def] using h
  have hf : rho.map (fun q : (P × F) × X => q.1.2) = nu := by
    have h := congrArg (fun m : Measure ((P × X) × F) => m.map Prod.snd) hr
    rw [Measure.map_map measurable_snd (by fun_prop)] at h
    simpa [Function.comp_def] using h
  apply (indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)).2
  change rho.map (fun q : (P × F) × X => ((q.1.1, q.2), q.1.2)) = _
  rw [hp, hf]
  exact hr

theorem map_reorder_conditionalCopies {O : Type*} [MeasurableSpace O]
    (mu : Measure P) (nu : Measure F) [SFinite mu] [SFinite nu]
    (eta : Kernel (P × F) O) [IsSFiniteKernel eta]
    (past : O → X) (hpast : Measurable past)
    (kappa : Kernel P X) [IsSFiniteKernel kappa]
    (h : (fun p : P × F => (eta.map past) p) =ᵐ[mu.prod nu]
      (fun p => kappa p.1)) :
    ((mu.prod nu) ⊗ₘ (eta ×ₖ eta)).map
        (fun q : (P × F) × (O × O) =>
          ((q.1.1, (past q.2.1, past q.2.2)), q.1.2)) =
      (mu ⊗ₘ (kappa ×ₖ kappa)).prod nu := by
  have hcopy : (fun p : P × F => ((eta.map past) ×ₖ (eta.map past)) p) =ᵐ[mu.prod nu]
      (fun p => (kappa ×ₖ kappa) p.1) := by
    filter_upwards [h] with p hp
    simp only [Kernel.prod_apply, hp]
  have hc := map_reorder_compProd_of_ae mu nu (kappa ×ₖ kappa)
    ((eta.map past) ×ₖ (eta.map past)) hcopy
  rw [Kernel.map_prod_map eta eta hpast hpast,
    Measure.compProd_map (hpast.prodMap hpast)] at hc
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at hc
  simpa [Function.comp_def, Prod.map] using hc

theorem indepFun_future_conditionalCopies {O : Type*} [MeasurableSpace O]
    (mu : Measure P) (nu : Measure F)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (eta : Kernel (P × F) O) [IsMarkovKernel eta]
    (past : O → X) (hpast : Measurable past)
    (kappa : Kernel P X) [IsMarkovKernel kappa]
    (h : (fun p : P × F => (eta.map past) p) =ᵐ[mu.prod nu]
      (fun p => kappa p.1)) :
    IndepFun (fun q : (P × F) × (O × O) =>
      (q.1.1, (past q.2.1, past q.2.2))) (fun q => q.1.2)
      ((mu.prod nu) ⊗ₘ (eta ×ₖ eta)) := by
  let rho := (mu.prod nu) ⊗ₘ (eta ×ₖ eta)
  have hr := map_reorder_conditionalCopies mu nu eta past hpast kappa h
  have hp : rho.map (fun q : (P × F) × (O × O) =>
      (q.1.1, (past q.2.1, past q.2.2))) = mu ⊗ₘ (kappa ×ₖ kappa) := by
    have hh := congrArg (fun m : Measure ((P × (X × X)) × F) => m.map Prod.fst) hr
    rw [Measure.map_map measurable_fst (by fun_prop)] at hh
    simpa [Function.comp_def, rho] using hh
  have hf : rho.map (fun q : (P × F) × (O × O) => q.1.2) = nu := by
    have hh := congrArg (fun m : Measure ((P × (X × X)) × F) => m.map Prod.snd) hr
    rw [Measure.map_map measurable_snd (by fun_prop)] at hh
    simpa [Function.comp_def, rho] using hh
  apply (indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)).2
  change rho.map (fun q : (P × F) × (O × O) =>
    ((q.1.1, (past q.2.1, past q.2.2)), q.1.2)) = _
  rw [hp, hf]
  exact hr

theorem map_conditionalCopies_of_jointLaw {W O : Type*}
    [MeasurableSpace W] [MeasurableSpace O]
    (rho : Measure W) [SFinite rho]
    (mu : Measure P) (nu : Measure F) [SFinite mu] [SFinite nu]
    (p : W → P) (hp : Measurable p) (future : W → F) (hf : Measurable future)
    (hlaw : rho.map (fun w => (p w, future w)) = mu.prod nu)
    (eta : Kernel W O) [IsSFiniteKernel eta]
    (past : O → X) (hpast : Measurable past)
    (kappa : Kernel P X) [IsSFiniteKernel kappa]
    (h : (fun w => (eta.map past) w) =ᵐ[rho] (fun w => kappa (p w))) :
    (rho ⊗ₘ (eta ×ₖ eta)).map
        (fun q : W × (O × O) =>
          ((p q.1, (past q.2.1, past q.2.2)), future q.1)) =
      (mu ⊗ₘ (kappa ×ₖ kappa)).prod nu := by
  have hcopy : (fun w => ((eta ×ₖ eta).map (Prod.map past past)) w) =ᵐ[rho]
      (fun w => ((kappa ×ₖ kappa).comap Prod.fst measurable_fst :
        Kernel (P × F) (X × X)) (p w, future w)) := by
    filter_upwards [h] with w hw
    rw [← Kernel.map_prod_map eta eta hpast hpast]
    simp only [Kernel.prod_apply, Kernel.comap_apply, hw]
  have hpush := map_compProd_of_kernel_map_ae rho (fun w => (p w, future w))
    (hp.prodMk hf) (Prod.map past past) (hpast.prodMap hpast)
    (eta ×ₖ eta) ((kappa ×ₖ kappa).comap Prod.fst measurable_fst) hcopy
  have hm := congrArg (fun m : Measure ((P × F) × (X × X)) =>
    m.map (fun q => ((q.1.1, q.2), q.1.2))) hpush
  rw [Measure.map_map (by fun_prop) (by fun_prop), hlaw,
    map_reorder_compProd mu nu (kappa ×ₖ kappa)] at hm
  simpa [Function.comp_def, Prod.map] using hm

theorem indepFun_of_joint_product {W : Type*} [MeasurableSpace W]
    (rho : Measure W) [IsFiniteMeasure rho]
    (mu : Measure P) (nu : Measure F)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (p : W → P) (hp : Measurable p) (future : W → F) (hf : Measurable future)
    (hlaw : rho.map (fun w => (p w, future w)) = mu.prod nu) :
    IndepFun p future rho := by
  have hplaw : rho.map p = mu := by
    have hh := congrArg (fun m : Measure (P × F) => m.map Prod.fst) hlaw
    rw [Measure.map_map measurable_fst (hp.prodMk hf)] at hh
    simpa [Function.comp_def] using hh
  have hflaw : rho.map future = nu := by
    have hh := congrArg (fun m : Measure (P × F) => m.map Prod.snd) hlaw
    rw [Measure.map_map measurable_snd (hp.prodMk hf)] at hh
    simpa [Function.comp_def] using hh
  apply (indepFun_iff_map_prod_eq_prod_map_map hp.aemeasurable hf.aemeasurable).2
  rw [hplaw, hflaw]
  exact hlaw

theorem indepFun_future_conditionalCopies_of_jointLaw {W O : Type*}
    [MeasurableSpace W] [MeasurableSpace O]
    (rho : Measure W) [IsProbabilityMeasure rho]
    (mu : Measure P) (nu : Measure F)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (p : W → P) (hp : Measurable p) (future : W → F) (hf : Measurable future)
    (hlaw : rho.map (fun w => (p w, future w)) = mu.prod nu)
    (eta : Kernel W O) [IsMarkovKernel eta]
    (past : O → X) (hpast : Measurable past)
    (kappa : Kernel P X) [IsMarkovKernel kappa]
    (h : (fun w => (eta.map past) w) =ᵐ[rho] (fun w => kappa (p w))) :
    IndepFun (fun q : W × (O × O) => (p q.1, (past q.2.1, past q.2.2)))
      (fun q => future q.1) (rho ⊗ₘ (eta ×ₖ eta)) := by
  apply indepFun_of_joint_product (rho ⊗ₘ (eta ×ₖ eta))
    (mu ⊗ₘ (kappa ×ₖ kappa)) nu _ (by fun_prop) _ (by fun_prop)
  exact map_conditionalCopies_of_jointLaw rho mu nu p hp future hf hlaw
    eta past hpast kappa h

def reorderEquiv : ((P × F) × X) ≃ᵐ ((P × X) × F) where
  toFun q := ((q.1.1, q.2), q.1.2)
  invFun q := ((q.1.1, q.2), q.1.2)
  left_inv q := rfl
  right_inv q := rfl
  measurable_toFun := by
    change Measurable (fun q : (P × F) × X => ((q.1.1, q.2), q.1.2))
    fun_prop
  measurable_invFun := by
    change Measurable (fun q : (P × X) × F => ((q.1.1, q.2), q.1.2))
    fun_prop

theorem exists_past_kernel_of_indep {O : Type*} [MeasurableSpace O]
    [StandardBorelSpace X] [Nonempty X]
    (mu : Measure P) (nu : Measure F)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (eta : Kernel (P × F) O) [IsMarkovKernel eta]
    (past : O → X) (hpast : Measurable past)
    (hind : IndepFun (fun q : (P × F) × O => (q.1.1, past q.2))
      (fun q => q.1.2) ((mu.prod nu) ⊗ₘ eta)) :
    ∃ kappa : Kernel P X, IsMarkovKernel kappa ∧
      (fun q : P × F => (eta.map past) q) =ᵐ[mu.prod nu] (fun q => kappa q.1) := by
  let rho := (mu.prod nu) ⊗ₘ eta
  let lam := rho.map (fun q : (P × F) × O => (q.1.1, past q.2))
  have hbase : rho.map Prod.fst = mu.prod nu := Measure.fst_compProd _ _
  have hfirst : lam.fst = mu := by
    change (rho.map (fun q : (P × F) × O => (q.1.1, past q.2))).map Prod.fst = mu
    rw [Measure.map_map measurable_fst (by fun_prop)]
    change rho.map (Prod.fst ∘ Prod.fst) = mu
    rw [← Measure.map_map measurable_fst measurable_fst, hbase]
    simp
  have hfuture : rho.map (fun q : (P × F) × O => q.1.2) = nu := by
    change rho.map (Prod.snd ∘ Prod.fst) = nu
    rw [← Measure.map_map measurable_snd measurable_fst, hbase]
    simp
  let kappa : Kernel P X := lam.condKernel
  have hdis : mu ⊗ₘ kappa = lam := by
    rw [← hfirst]
    exact Measure.disintegrate lam lam.condKernel
  have horiginal : rho.map (fun q : (P × F) × O =>
      ((q.1.1, past q.2), q.1.2)) = lam.prod nu := by
    rw [hind.map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)]
    change lam.prod (rho.map (fun q : (P × F) × O => q.1.2)) = lam.prod nu
    rw [hfuture]
  have hobs : ((mu.prod nu) ⊗ₘ eta.map past).map
      (reorderEquiv : ((P × F) × X) ≃ᵐ ((P × X) × F)) = lam.prod nu := by
    rw [Measure.compProd_map hpast,
      Measure.map_map (reorderEquiv.measurable) (by fun_prop)]
    exact horiginal
  have hnew : ((mu.prod nu) ⊗ₘ kappa.comap Prod.fst measurable_fst).map
      (reorderEquiv : ((P × F) × X) ≃ᵐ ((P × X) × F)) = lam.prod nu := by
    change ((mu.prod nu) ⊗ₘ kappa.comap Prod.fst measurable_fst).map
      (fun q : (P × F) × X => ((q.1.1, q.2), q.1.2)) = lam.prod nu
    rw [map_reorder_compProd, hdis]
  have heq : (mu.prod nu) ⊗ₘ eta.map past =
      (mu.prod nu) ⊗ₘ kappa.comap Prod.fst measurable_fst :=
    reorderEquiv.measurableEmbedding.map_injective (hobs.trans hnew.symm)
  have hk := Kernel.ae_eq_of_compProd_eq heq
  exact ⟨kappa, inferInstance, hk⟩

theorem indepFun_future_conditionalCopies_of_original_indep {O : Type*}
    [MeasurableSpace O] [StandardBorelSpace X] [Nonempty X]
    (mu : Measure P) (nu : Measure F)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (eta : Kernel (P × F) O) [IsMarkovKernel eta]
    (past : O → X) (hpast : Measurable past)
    (hind : IndepFun (fun q : (P × F) × O => (q.1.1, past q.2))
      (fun q => q.1.2) ((mu.prod nu) ⊗ₘ eta)) :
    IndepFun (fun q : (P × F) × (O × O) =>
      (q.1.1, (past q.2.1, past q.2.2))) (fun q => q.1.2)
      ((mu.prod nu) ⊗ₘ (eta ×ₖ eta)) := by
  obtain ⟨kappa, hkappa, h⟩ := exists_past_kernel_of_indep mu nu eta past hpast hind
  let := hkappa
  exact indepFun_future_conditionalCopies mu nu eta past hpast kappa h

theorem exists_past_kernel_of_indep_of_embedding {W O : Type*}
    [MeasurableSpace W] [MeasurableSpace O]
    [StandardBorelSpace X] [Nonempty X]
    (rho : Measure W) [IsProbabilityMeasure rho]
    (mu : Measure P) (nu : Measure F)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (p : W → P) (hp : Measurable p) (future : W → F) (hf : Measurable future)
    (hsplit : MeasurableEmbedding (fun w => (p w, future w)))
    (hlaw : rho.map (fun w => (p w, future w)) = mu.prod nu)
    (eta : Kernel W O) [IsMarkovKernel eta]
    (past : O → X) (hpast : Measurable past)
    (hind : IndepFun (fun q : W × O => (p q.1, past q.2))
      (fun q => future q.1) (rho ⊗ₘ eta)) :
    ∃ kappa : Kernel P X, IsMarkovKernel kappa ∧
      (fun w => (eta.map past) w) =ᵐ[rho] (fun w => kappa (p w)) := by
  let joint := rho ⊗ₘ eta
  let lam := joint.map (fun q : W × O => (p q.1, past q.2))
  have hbase : joint.map Prod.fst = rho := Measure.fst_compProd _ _
  have hplaw : rho.map p = mu := by
    have h := congrArg (fun m : Measure (P × F) => m.map Prod.fst) hlaw
    rw [Measure.map_map measurable_fst (hp.prodMk hf)] at h
    simpa [Function.comp_def] using h
  have hflaw : rho.map future = nu := by
    have h := congrArg (fun m : Measure (P × F) => m.map Prod.snd) hlaw
    rw [Measure.map_map measurable_snd (hp.prodMk hf)] at h
    simpa [Function.comp_def] using h
  have hfirst : lam.fst = mu := by
    change (joint.map (fun q : W × O => (p q.1, past q.2))).map Prod.fst = mu
    rw [Measure.map_map measurable_fst (by fun_prop)]
    change joint.map (p ∘ Prod.fst) = mu
    rw [← Measure.map_map hp measurable_fst, hbase, hplaw]
  have hfuture : joint.map (fun q : W × O => future q.1) = nu := by
    change joint.map (future ∘ Prod.fst) = nu
    rw [← Measure.map_map hf measurable_fst, hbase, hflaw]
  let kappa : Kernel P X := lam.condKernel
  have hdis : mu ⊗ₘ kappa = lam := by
    rw [← hfirst]
    exact Measure.disintegrate lam lam.condKernel
  have horiginal : joint.map (fun q : W × O =>
      ((p q.1, past q.2), future q.1)) = lam.prod nu := by
    rw [hind.map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)]
    change lam.prod (joint.map (fun q : W × O => future q.1)) = lam.prod nu
    rw [hfuture]
  have hobs : (rho ⊗ₘ eta.map past).map
      (fun q : W × X => ((p q.1, q.2), future q.1)) = lam.prod nu := by
    rw [Measure.compProd_map hpast, Measure.map_map (by fun_prop) (by fun_prop)]
    exact horiginal
  have htransport : (rho ⊗ₘ kappa.comap p hp).map
      (Prod.map (fun w => (p w, future w)) id) =
      rho.map (fun w => (p w, future w)) ⊗ₘ
        kappa.comap Prod.fst measurable_fst :=
    map_compProd_comap rho (fun w => (p w, future w)) (hp.prodMk hf)
      (kappa.comap Prod.fst measurable_fst)
  have hnew : (rho ⊗ₘ kappa.comap p hp).map
      (fun q : W × X => ((p q.1, q.2), future q.1)) = lam.prod nu := by
    have h := congrArg (fun m : Measure ((P × F) × X) =>
      m.map (reorderEquiv : ((P × F) × X) ≃ᵐ ((P × X) × F))) htransport
    rw [Measure.map_map (reorderEquiv.measurable) (by fun_prop), hlaw] at h
    change (rho ⊗ₘ kappa.comap p hp).map
      (fun q : W × X => ((p q.1, q.2), future q.1)) =
      ((mu.prod nu) ⊗ₘ kappa.comap Prod.fst measurable_fst).map
        (fun q : (P × F) × X => ((q.1.1, q.2), q.1.2)) at h
    rw [map_reorder_compProd, hdis] at h
    exact h
  have hemb : MeasurableEmbedding (fun q : W × X => ((p q.1, q.2), future q.1)) :=
    reorderEquiv.measurableEmbedding.comp (hsplit.prodMap MeasurableEmbedding.id)
  have heq : rho ⊗ₘ eta.map past = rho ⊗ₘ kappa.comap p hp :=
    hemb.map_injective (hobs.trans hnew.symm)
  exact ⟨kappa, inferInstance, Kernel.ae_eq_of_compProd_eq heq⟩

theorem indepFun_future_conditionalCopies_of_embedding {W O : Type*}
    [MeasurableSpace W] [MeasurableSpace O]
    [StandardBorelSpace X] [Nonempty X]
    (rho : Measure W) [IsProbabilityMeasure rho]
    (mu : Measure P) (nu : Measure F)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (p : W → P) (hp : Measurable p) (future : W → F) (hf : Measurable future)
    (hsplit : MeasurableEmbedding (fun w => (p w, future w)))
    (hlaw : rho.map (fun w => (p w, future w)) = mu.prod nu)
    (eta : Kernel W O) [IsMarkovKernel eta]
    (past : O → X) (hpast : Measurable past)
    (hind : IndepFun (fun q : W × O => (p q.1, past q.2))
      (fun q => future q.1) (rho ⊗ₘ eta)) :
    IndepFun (fun q : W × (O × O) => (p q.1, (past q.2.1, past q.2.2)))
      (fun q => future q.1) (rho ⊗ₘ (eta ×ₖ eta)) := by
  obtain ⟨kappa, hkappa, h⟩ := exists_past_kernel_of_indep_of_embedding
    rho mu nu p hp future hf hsplit hlaw eta past hpast hind
  let := hkappa
  exact indepFun_future_conditionalCopies_of_jointLaw rho mu nu p hp future hf hlaw
    eta past hpast kappa h

theorem indepFun_future_conditionalCopies_of_reconstructible_split {W O : Type*}
    [MeasurableSpace W] [MeasurableSpace O]
    [StandardBorelSpace X] [Nonempty X]
    (rho : Measure W) [IsProbabilityMeasure rho]
    (p : W → P) (hp : Measurable p) (future : W → F) (hf : Measurable future)
    (hsplit : MeasurableEmbedding (fun w => (p w, future w)))
    (eta : Kernel W O) [IsMarkovKernel eta]
    (past : O → X) (hpast : Measurable past)
    (hind : IndepFun (fun q : W × O => (p q.1, past q.2))
      (fun q => future q.1) (rho ⊗ₘ eta)) :
    IndepFun (fun q : W × (O × O) => (p q.1, (past q.2.1, past q.2.2)))
      (fun q => future q.1) (rho ⊗ₘ (eta ×ₖ eta)) := by
  have hbaseind : IndepFun (fun q : W × O => p q.1)
      (fun q => future q.1) (rho ⊗ₘ eta) := hind.comp measurable_fst measurable_id
  have hlaw := hbaseind.map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)
  change (rho ⊗ₘ eta).map ((fun w => (p w, future w)) ∘ Prod.fst) =
    ((rho ⊗ₘ eta).map (p ∘ Prod.fst)).prod
      ((rho ⊗ₘ eta).map (future ∘ Prod.fst)) at hlaw
  rw [← Measure.map_map (hp.prodMk hf) measurable_fst,
    ← Measure.map_map hp measurable_fst, ← Measure.map_map hf measurable_fst] at hlaw
  change ((rho ⊗ₘ eta).fst.map (fun w => (p w, future w))) =
    ((rho ⊗ₘ eta).fst.map p).prod ((rho ⊗ₘ eta).fst.map future) at hlaw
  rw [Measure.fst_compProd] at hlaw
  exact indepFun_future_conditionalCopies_of_embedding rho (rho.map p) (rho.map future)
    p hp future hf hsplit hlaw eta past hpast hind

end Problem367.KernelCompatibility

end

end OAI
