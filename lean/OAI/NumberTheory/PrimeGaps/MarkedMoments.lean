import OAI.NumberTheory.PrimeGaps.ProfileSymmetry

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem orderedWeight_marked_limit (hBV : BombieriVinogradov) {tau lam : ℝ} {k : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : AdmissibleFamily tau k f)
    (htau : 0≤tau) (htau2 : 2*tau<1/2) (hlam : 0<lam) :
    Tendsto (fun X : ℕ => average X (fun m => orderedWeight tau lam k f X m^2*
      orderedDetector X (blockLength lam X) m))
      atTop (𝓝 (lam*familyW lam k f)) := by
  classical
  let H := fun (j : Fin (k+1)) X m => weightedBlock X (blockLength lam X) (blockLength lam X+1)
       (cumulativeProfile tau (f j)) (subsetCoefficient j) m
  have hp (i j : Fin (k+1)) :
      Tendsto (fun X : ℕ => average X (fun m => H i X m*H j X m*orderedDetector X (blockLength lam X) m)) atTop
        (𝓝 (if i=j then lam*alpha lam i*l2Mass (f i) else 0)) := by
    have hfi := hf.2.1 i (by omega : (i:ℕ)≤k)
    have hfj := hf.2.1 j (by omega : (j:ℕ)≤k)
    by_cases hij : i=j
    · subst j
      simp only [↓reduceIte]
      simpa only [H,pow_two] using marked_cumulative_square_limit hBV htau htau2 hlam
        (f i) hfi.2.1 hfi.1 hfi.2.2.1 hfi.2.2.2
    · simp only [ite_eq_right hij]
      have hne : (i:ℕ)≠(j:ℕ) := fun h => hij (Fin.ext h)
      exact marked_cumulative_cross_limit hBV hne htau htau2 hlam
        (f i) (f j) hfi.2.1 hfj.2.1 hfi.1 hfj.1 hfi.2.2.1 hfj.2.2.1
  have hs := tendsto_finsetSum Finset.univ fun i _ =>
    tendsto_finsetSum Finset.univ fun j _ => hp i j
  have he (X : ℕ) : average X (fun m => orderedWeight tau lam k f X m^2*orderedDetector X (blockLength lam X) m)=
      ∑ i : Fin (k+1),∑ j : Fin (k+1),average X (fun m => H i X m*H j X m*orderedDetector X (blockLength lam X) m) := by
    unfold orderedWeight
    simp only [pow_two,Finset.sum_mul,Finset.mul_sum,average_finset_sum]
    rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte] at hs
  have hv : (∑ i : Fin (k+1),lam*alpha lam i*l2Mass (f i))=lam*familyW lam k f := by
    simp only [mul_assoc,←Finset.mul_sum]
    congr 1
    exact Fin.sum_univ_eq_sum_range (fun j : ℕ => alpha lam j*l2Mass (f j)) (k+1)
  rw [hv] at hs
  exact hs.congr' (Eventually.of_forall fun X => (he X).symm)

theorem deleteCoordinate_smooth {n : ℕ} (f : (Fin (n+1) → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (deleteCoordinate f) := by
  let K := (fun v : Fin (n+1) → ℝ => -v (Fin.last n)) '' tsupport f
  have hK : IsCompact K := hf.isCompact.image (continuous_apply _ |>.neg)
  let g : (Fin n → ℝ) → ℝ → ℝ := fun t u => f (Fin.snoc t (-u))
  have hgs : ∀ t u,t∈(Set.univ : Set (Fin n → ℝ)) → u∉K → g t u=0 := by
    intro t u _ hu
    by_contra hn
    apply hu
    refine ⟨Fin.snoc t (-u),subset_tsupport f hn,?_⟩
    simp
  have hsm : ContDiff ℝ ∞ (fun p : (Fin n → ℝ) × ℝ => (Fin.snoc p.1 (-p.2) : Fin (n+1) → ℝ)) := by
    apply contDiff_pi.mpr
    intro i
    cases i using Fin.lastCases with
    | last => simpa using contDiff_snd.neg
    | cast i => simpa [Function.comp_def] using (contDiff_apply ℝ ℝ i).comp contDiff_fst
  have hh := MeasureTheory.contDiffOn_convolution_right_with_param
    (μ:=volume) (ContinuousLinearMap.mul ℝ ℝ) isOpen_univ hK hgs
    (f:=fun _ : ℝ => (1:ℝ)) (continuous_const.locallyIntegrable) (hfs.comp hsm).contDiffOn
  have hg : ContDiff ℝ ∞ (fun p : (Fin n → ℝ) × ℝ =>
      ((fun _ : ℝ => (1:ℝ)) ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] g p.1) p.2) := by
    rwa [Set.univ_prod_univ,contDiffOn_univ] at hh
  have H := hg.comp (contDiff_id.prodMk (contDiff_const (c:=(0:ℝ))))
  change ContDiff ℝ ∞ (fun x => ∫ t : ℝ, f (Fin.snoc x t))
  simpa only [Function.comp_def,convolution_def,ContinuousLinearMap.mul_apply',one_mul,
    zero_sub,g,neg_neg,deleteCoordinate,id_eq] using H

theorem deleteCoordinate_tsupport_subset {n : ℕ} (f : (Fin (n+1) → ℝ) → ℝ)
    (hf : HasCompactSupport f) :
    tsupport (deleteCoordinate f) ⊆
      (fun v : Fin (n+1) → ℝ => fun i : Fin n => v i.castSucc) '' tsupport f := by
  have hk := hf.isCompact.image (continuous_pi (fun i : Fin n => continuous_apply i.castSucc))
  apply closure_minimal _ hk.isClosed
  intro t ht
  by_contra hn
  apply ht
  unfold deleteCoordinate
  apply integral_eq_zero_of_ae
  filter_upwards [] with u
  by_contra hfu
  exact hn ⟨Fin.snoc t u,subset_tsupport f hfu,by ext i; simp⟩

theorem deleteCoordinate_compact {n : ℕ} (f : (Fin (n+1) → ℝ) → ℝ)
    (hf : HasCompactSupport f) : HasCompactSupport (deleteCoordinate f) := by
  exact (hf.isCompact.image (continuous_pi (fun i : Fin n => continuous_apply i.castSucc))).of_isClosed_subset
    (isClosed_tsupport _) (deleteCoordinate_tsupport_subset f hf)

theorem deleteCoordinate_interior_support {n : ℕ} {tau : ℝ}
    (f : (Fin (n+1) → ℝ) → ℝ) (hf : HasCompactSupport f)
    (hs : tsupport f⊆positiveSimplex (n+1) tau) :
    tsupport (deleteCoordinate f) ⊆positiveSimplex n tau := by
  intro t ht
  obtain ⟨v,hv,rfl⟩ := deleteCoordinate_tsupport_subset f hf ht
  have hv' := hs hv
  refine ⟨fun i => hv'.1 i.castSucc,?_⟩
  have hh : coordinateSum v=coordinateSum (fun i : Fin n => v i.castSucc)+v (Fin.last n) := by
    exact Fin.sum_univ_castSucc (fun i => v i)
  have hp := hv'.1 (Fin.last n)
  linarith [hv'.2]

noncomputable def fixLastPerm {n : ℕ} (e : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+1)) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr e (Equiv.refl (Fin 1))).trans finSumFinEquiv)

@[simp] theorem fixLastPerm_castSucc {n : ℕ} (e : Equiv.Perm (Fin n)) (i : Fin n) :
    fixLastPerm e i.castSucc=(e i).castSucc := by
  change finSumFinEquiv ((Equiv.sumCongr e (Equiv.refl (Fin 1)))
    (finSumFinEquiv.symm (Fin.castAdd 1 i)))=Fin.castAdd 1 (e i)
  simp

@[simp] theorem fixLastPerm_last {n : ℕ} (e : Equiv.Perm (Fin n)) :
    fixLastPerm e (Fin.last n)=Fin.last n := by
  change finSumFinEquiv ((Equiv.sumCongr e (Equiv.refl (Fin 1)))
    (finSumFinEquiv.symm (Fin.natAdd n (0 : Fin 1))))=Fin.natAdd n (0 : Fin 1)
  simp

theorem deleteCoordinate_symmetric {n : ℕ} (f : (Fin (n+1) → ℝ) → ℝ)
    (hs : SymmetricFunction f) : SymmetricFunction (deleteCoordinate f) := by
  intro e t
  unfold deleteCoordinate
  apply integral_congr_ae
  filter_upwards [] with u
  have he : Fin.snoc (t ∘ e) u=(Fin.snoc t u : Fin (n+1) → ℝ) ∘ fixLastPerm e := by
    ext i
    cases i using Fin.lastCases <;> simp
  rw [he,hs]

theorem pi_restrict_Ici {n : ℕ} (v : Fin n → ℝ) :
    Measure.pi (fun i => volume.restrict (Ici (v i)))=volume.restrict (Ici v) := by
  rw [←Measure.restrict_pi_pi]
  congr 1
  ext x
  simp

theorem integral_Ici_snoc {n : ℕ} (v : Fin (n+1) → ℝ)
    (f : (Fin (n+1) → ℝ) → ℝ) (hf : IntegrableOn f (Ici v)) :
    (∫ x in Ici v,f x)=∫ y in Ici (fun i : Fin n => v i.castSucc),
      ∫ a in Ici (v (Fin.last n)),f (Fin.snoc y a) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) (Fin.last n)
  have hm := measurePreserving_piFinSuccAbove
    (fun i : Fin (n+1) => volume.restrict (Ici (v i))) (Fin.last n)
  have he : ∀ p : ℝ × (Fin n → ℝ), e.symm p=Fin.snoc p.2 p.1 := by
    intro p
    simp [e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv]
  have hfi : Integrable f (Measure.pi (fun i => volume.restrict (Ici (v i)))) := by
    rw [pi_restrict_Ici]
    exact hf
  have hh := hm.symm.integral_comp' f
  have hi := (hm.symm.integrable_comp_emb e.symm.measurableEmbedding).mpr hfi
  dsimp only [e] at he
  simp only [Fin.succAbove_last_apply,he,Function.comp_def,pi_restrict_Ici] at hh hi
  rw [←hh]
  exact integral_prod_symm _ hi

theorem cumulativeProfile_delete_tail {n : ℕ} {tau : ℝ}
    (f : (Fin (n+1) → ℝ) → ℝ) (hf : HasCompactSupport f)
    (hfs : ContDiff ℝ ∞ f) (hs : tsupport f⊆positiveSimplex (n+1) tau)
    (v : Fin n → ℝ) (hv : ∀ i,0≤v i) :
    cumulativeProfile tau f (Fin.snoc v 0)=cumulativeProfile tau (deleteCoordinate f) v := by
  have hs' := deleteCoordinate_interior_support f hf hs
  rw [cumulativeProfile_tail tau f hs,cumulativeProfile_tail tau _ hs' _ hv]
  · rw [integral_Ici_snoc _ _ (hfs.continuous.integrable_of_hasCompactSupport hf).integrableOn]
    simp only [Fin.snoc_castSucc,Fin.snoc_last]
    apply setIntegral_congr_fun measurableSet_Ici
    intro t _
    exact (deleteCoordinate_eq_orthant_integral (fun _ h => (hs (subset_tsupport f h)).1) t).symm
  · intro i
    cases i using Fin.lastCases <;> simp [hv]

noncomputable def deletedFamily (f : (j : ℕ) → (Fin j → ℝ) → ℝ)
    (j : ℕ) (t : Fin j → ℝ) : ℝ := f j t+deleteCoordinate (f (j+1)) t

theorem AdmissibleFamily.all_properties {tau : ℝ} {k : ℕ}
    {f : (j : ℕ) → (Fin j → ℝ) → ℝ} (hf : AdmissibleFamily tau k f) (j : ℕ) :
    ContDiff ℝ ∞ (f j) ∧ HasCompactSupport (f j) ∧
    tsupport (f j)⊆positiveSimplex j tau ∧ SymmetricFunction (f j) := by
  by_cases hj : j≤k
  · exact hf.2.1 j hj
  · rw [hf.2.2 j (by omega)]
    refine ⟨contDiff_const,HasCompactSupport.zero,by simp,?_⟩
    intro e v
    rfl

theorem deletedFamily_admissible {tau : ℝ} {k : ℕ}
    {f : (j : ℕ) → (Fin j → ℝ) → ℝ} (hf : AdmissibleFamily tau k f) :
    AdmissibleFamily tau k (deletedFamily f) := by
  refine ⟨hf.1,?_,?_⟩
  · intro j _
    obtain ⟨hjs,hjc,hjt,hjy⟩ := hf.all_properties j
    obtain ⟨hns,hnc,hnt,hny⟩ := hf.all_properties (j+1)
    refine ⟨hjs.add (deleteCoordinate_smooth _ hnc hns),
      hjc.add (deleteCoordinate_compact _ hnc),?_,?_⟩
    · exact (tsupport_add (f j) (deleteCoordinate (f (j+1)))).trans
        (Set.union_subset hjt (deleteCoordinate_interior_support _ hnc hnt))
    · intro e v
      exact congrArg₂ (·+·) (hjy e v) (deleteCoordinate_symmetric _ hny e v)
  · intro j hj
    have h1 := hf.2.2 j hj
    have h2 := hf.2.2 (j+1) (by omega)
    ext t
    simp [deletedFamily,h1,h2]

theorem cumulativeProfile_deletedFamily {tau : ℝ} {k : ℕ}
    {f : (j : ℕ) → (Fin j → ℝ) → ℝ} (hf : AdmissibleFamily tau k f)
    (j : ℕ) (v : Fin j → ℝ) (hv : ∀ i,0≤v i) :
    cumulativeProfile tau (deletedFamily f j) v=
      cumulativeProfile tau (f j) v+cumulativeProfile tau (f (j+1)) (Fin.snoc v 0) := by
  obtain ⟨hjs,hjc,hjt,hjy⟩ := hf.all_properties j
  obtain ⟨hns,hnc,hnt,hny⟩ := hf.all_properties (j+1)
  have hg := (deletedFamily_admissible hf).all_properties j
  rw [cumulativeProfile_delete_tail _ hnc hns hnt v hv,
    cumulativeProfile_tail tau _ hg.2.2.1 _ hv,cumulativeProfile_tail tau _ hjt _ hv,
    cumulativeProfile_tail tau _ (deleteCoordinate_interior_support _ hnc hnt) _ hv]
  exact integral_add (hjs.continuous.integrable_of_hasCompactSupport hjc).integrableOn
    ((deleteCoordinate_smooth _ hnc hns).continuous.integrable_of_hasCompactSupport
      (deleteCoordinate_compact _ hnc)).integrableOn

theorem divisorSum_add {n : ℕ} (X M : ℕ) (F G : (Fin n → ℝ) → ℝ) (b : Fin n → ℕ) :
    divisorSum X (F+G) M b=divisorSum X F M b+divisorSum X G M b := by
  simp only [divisorSum,divisorCoefficient,Pi.add_apply,mul_add,Finset.sum_add_distrib]

theorem divisorSum_internal_family_delete {tau : ℝ} {k X M a : ℕ}
    {f : (j : ℕ) → (Fin j → ℝ) → ℝ} (hf : AdmissibleFamily tau k f)
    (htau : tau<1) (hX : 2≤X) (hM : X<M+a) (hp : Nat.Prime (M+a))
    (j : ℕ) (b : Fin j → ℕ) :
    divisorSum X (cumulativeProfile tau (f j)) M b+
      divisorSum X (cumulativeProfile tau (f (j+1))) M (Fin.snoc b a)=
      divisorSum X (cumulativeProfile tau (deletedFamily f j)) M b := by
  have hn := hf.all_properties (j+1)
  rw [divisorSum_prime_delete hX hM hp _ htau (cumulativeProfile_budget tau _ hn.2.2.1)]
  rw [←divisorSum_add]
  apply divisorSum_congr_orthant hX
  intro v hv
  exact (cumulativeProfile_deletedFamily hf j v hv).symm

theorem orderedDetector_eq_detector (X h m : ℕ) :
    orderedDetector X h m=detector X (Finset.Ioc 0 h) m := by
  unfold orderedDetector detector
  congr 1
  have he : Finset.Ioc 0 h=Finset.Ico 1 (h+1) := by
    ext i
    simp only [Finset.mem_Ioc,Finset.mem_Ico]
    omega
  rw [he,Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_right]
  exact Fin.sum_univ_eq_sum_range (fun c : ℕ => theta (m+(1+c))) h

theorem unorderedWeight_external_marked_limit (hBV : BombieriVinogradov) {tau lam : ℝ} {k : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : AdmissibleFamily tau k f)
    (htau : 0≤tau) (htau2 : 2*tau<1/2) (hlam : 0<lam) :
    Tendsto (fun X : ℕ => average X (fun m => unorderedWeight tau lam k f X m^2*
      detector X (Finset.Ioc 0 (blockLength lam X)) m))
      atTop (𝓝 (lam*familyW lam k f)) := by
  apply (orderedWeight_marked_limit hBV f hf htau htau2 hlam).congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  simp only [orderedWeight_eq_unordered f hf hX,orderedDetector_eq_detector]

noncomputable def setDivisor (F : (j : ℕ) → (Fin j → ℝ) → ℝ)
    (X M h a : ℕ) (S : Finset (Fin h)) : ℝ :=
  divisorSum X (F S.card) M (fun i => a+(subsetEnumeration ⟨S,rfl⟩ i:ℕ))

theorem subsetEnumeration_range {h n : ℕ} (S : {S : Finset (Fin h) // S.card=n}) :
    Set.range (subsetEnumeration S)=(S.val : Set (Fin h)) := by
  ext x
  have hh := Finset.ext_iff.mp (subsetEnumeration_image S) x
  simpa only [Set.mem_range,Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_coe] using hh

theorem setDivisor_eq_enumeration {X M h a n : ℕ} (hX : 2≤X)
    (F : (j : ℕ) → (Fin j → ℝ) → ℝ)
    (hF : ∀ j (e : Equiv.Perm (Fin j)) v,(∀ i,0≤v i) → F j (v ∘ e)=F j v)
    (S : Finset (Fin h)) (hn : S.card=n) (b : Fin n → Fin h)
    (hb : Function.Injective b) (hr : Set.range b=(S:Set (Fin h))) :
    setDivisor F X M h a S=divisorSum X (F n) M (fun i => a+(b i:ℕ)) := by
  subst n
  obtain ⟨e,he⟩ := injective_same_range_perm (subsetEnumeration ⟨S,rfl⟩) b hb
    ((subsetEnumeration_range ⟨S,rfl⟩).trans hr.symm)
  rw [he]
  exact (divisorSum_perm_orthant hX (F S.card) (hF S.card) e
    (fun i => a+(subsetEnumeration ⟨S,rfl⟩ i:ℕ))).symm

theorem snoc_subsetEnumeration_injective {h : ℕ} (S : Finset (Fin h)) {c : Fin h} (hc : c∉S) :
    Function.Injective (Fin.snoc (subsetEnumeration ⟨S,rfl⟩) c) := by
  intro i j hij
  cases i using Fin.lastCases with
  | last =>
    cases j using Fin.lastCases with
    | last => rfl
    | cast j =>
      simp only [Fin.snoc_last,Fin.snoc_castSucc] at hij
      have hj : subsetEnumeration ⟨S,rfl⟩ j∈S := by
        have hh : subsetEnumeration ⟨S,rfl⟩ j∈Set.range (subsetEnumeration ⟨S,rfl⟩) := ⟨j,rfl⟩
        rwa [subsetEnumeration_range] at hh
      exact False.elim (hc (hij.symm ▸ hj))
  | cast i =>
    cases j using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last,Fin.snoc_castSucc] at hij
      have hi : subsetEnumeration ⟨S,rfl⟩ i∈S := by
        have hh : subsetEnumeration ⟨S,rfl⟩ i∈Set.range (subsetEnumeration ⟨S,rfl⟩) := ⟨i,rfl⟩
        rwa [subsetEnumeration_range] at hh
      exact False.elim (hc (hij ▸ hi))
    | cast j =>
      simp only [Fin.snoc_castSucc] at hij
      exact congrArg Fin.castSucc ((subsetEnumeration ⟨S,rfl⟩).injective hij)

theorem snoc_subsetEnumeration_range {h : ℕ} (S : Finset (Fin h)) (c : Fin h) :
    Set.range (Fin.snoc (subsetEnumeration ⟨S,rfl⟩) c)=↑(insert c S : Finset (Fin h)) := by
  ext x
  simp only [Set.mem_range,Finset.mem_coe,Finset.mem_insert]
  constructor
  · rintro ⟨i,rfl⟩
    cases i using Fin.lastCases with
    | last => simp
    | cast i =>
      right
      simp only [Fin.snoc_castSucc]
      have hh : subsetEnumeration ⟨S,rfl⟩ i∈Set.range (subsetEnumeration ⟨S,rfl⟩) := ⟨i,rfl⟩
      rwa [subsetEnumeration_range] at hh
  · rintro (rfl | hx)
    · exact ⟨Fin.last _,by simp⟩
    · have hx' : x∈Set.range (subsetEnumeration ⟨S,rfl⟩) := by rwa [subsetEnumeration_range]
      obtain ⟨i,rfl⟩ := hx'
      exact ⟨i.castSucc,by simp⟩

theorem setDivisor_insert_eq_snoc {X M h a : ℕ} (hX : 2≤X)
    (F : (j : ℕ) → (Fin j → ℝ) → ℝ)
    (hF : ∀ j (e : Equiv.Perm (Fin j)) v,(∀ i,0≤v i) → F j (v ∘ e)=F j v)
    (S : Finset (Fin h)) {c : Fin h} (hc : c∉S) :
    setDivisor F X M h a (insert c S)=
      divisorSum X (F (S.card+1)) M
        (Fin.snoc (fun i => a+(subsetEnumeration ⟨S,rfl⟩ i:ℕ)) (a+(c:ℕ))) := by
  rw [setDivisor_eq_enumeration hX F hF _ (Finset.card_insert_of_notMem hc)
    _ (snoc_subsetEnumeration_injective S hc) (snoc_subsetEnumeration_range S c)]
  congr 1
  funext i
  cases i using Fin.lastCases <;> simp

noncomputable def finiteSubsetWeight (tau : ℝ) (f : (j : ℕ) → (Fin j → ℝ) → ℝ)
    (X M h a : ℕ) (B : Finset (Fin h)) : ℝ :=
  ∑ S∈B.powerset,setDivisor (fun j => cumulativeProfile tau (f j)) X M h a S

theorem finiteSubsetWeight_prime_delete {tau : ℝ} {k X M h a : ℕ}
    {f : (j : ℕ) → (Fin j → ℝ) → ℝ} (hf : AdmissibleFamily tau k f)
    (htau : tau<1) (hX : 2≤X) (c : Fin h) (hM : X<M+(a+(c:ℕ)))
    (hp : Nat.Prime (M+(a+(c:ℕ)))) :
    finiteSubsetWeight tau f X M h a Finset.univ=
      finiteSubsetWeight tau (deletedFamily f) X M h a (Finset.univ.erase c) := by
  classical
  have hsym : ∀ j (e : Equiv.Perm (Fin j)) v,(∀ i,0≤v i) →
      cumulativeProfile tau (f j) (v ∘ e)=cumulativeProfile tau (f j) v := by
    intro j
    have hj := hf.all_properties j
    exact cumulativeProfile_perm_orthant _ hj.2.2.1 hj.2.2.2
  have he : (Finset.univ : Finset (Fin h))=insert c (Finset.univ.erase c) := by simp
  unfold finiteSubsetWeight
  conv_lhs => rw [he,Finset.sum_powerset_insert (Finset.notMem_erase c Finset.univ),←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  have hc : c∉S := fun h => Finset.notMem_erase c Finset.univ ((Finset.mem_powerset.mp hS) h)
  rw [setDivisor_insert_eq_snoc hX _ hsym S hc]
  exact divisorSum_internal_family_delete hf htau hX hM hp S.card _

theorem setDivisor_fixed_card {X M h a n : ℕ}
    (F : (j : ℕ) → (Fin j → ℝ) → ℝ) (S : Finset (Fin h)) (hn : S.card=n) :
    setDivisor F X M h a S=
      divisorSum X (F n) M (fun i => a+(subsetEnumeration ⟨S,hn⟩ i:ℕ)) := by
  subst n
  rfl

theorem setDivisor_level_sum (X M h a n : ℕ)
    (F : (j : ℕ) → (Fin j → ℝ) → ℝ) :
    (∑ S ∈ Finset.powersetCard n (Finset.univ : Finset (Fin h)),setDivisor F X M h a S)=
      unorderedBlock X h a (F n) M := by
  classical
  rw [Finset.sum_subtype (p:=fun S : Finset (Fin h) => S.card=n)
    (Finset.powersetCard n Finset.univ) (by intro S; simp)]
  unfold unorderedBlock
  apply Finset.sum_congr rfl
  intro S _
  exact setDivisor_fixed_card F S.val S.property

@[simp] theorem cumulativeProfile_zero (tau : ℝ) (n : ℕ) :
    cumulativeProfile tau (0 : (Fin n → ℝ) → ℝ)=0 := by
  ext v
  simp [cumulativeProfile,cumulativeExtension,convolution_def]

@[simp] theorem divisorSum_zero (X M : ℕ) {n : ℕ} (b : Fin n → ℕ) :
    divisorSum X (0 : (Fin n → ℝ) → ℝ) M b=0 := by
  simp [divisorSum,divisorCoefficient]

@[simp] theorem unorderedBlock_zero (X h a M n : ℕ) :
    unorderedBlock X h a (0 : (Fin n → ℝ) → ℝ) M=0 := by
  simp [unorderedBlock]

theorem finiteSubsetWeight_eq_unordered_levels {tau : ℝ} {k X M h a : ℕ}
    {f : (j : ℕ) → (Fin j → ℝ) → ℝ} (hf : AdmissibleFamily tau k f) (hk : k≤h) :
    finiteSubsetWeight tau f X M h a Finset.univ=
      ∑ j : Fin (k+1),unorderedBlock X h a (cumulativeProfile tau (f j)) M := by
  unfold finiteSubsetWeight
  rw [Finset.sum_powerset]
  simp only [Finset.card_univ,Fintype.card_fin,setDivisor_level_sum]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => unorderedBlock X h a (cumulativeProfile tau (f j)) M) (k+1)]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega : k+1≤h+1))
  intro j _ hj
  have hjk : k<j := by simp only [Finset.mem_range,not_lt] at hj; omega
  rw [hf.2.2 j hjk,cumulativeProfile_zero,unorderedBlock_zero]

theorem unorderedWeight_eq_finiteSubsetWeight {tau lam : ℝ} {k X M : ℕ}
    {f : (j : ℕ) → (Fin j → ℝ) → ℝ} (hf : AdmissibleFamily tau k f)
    (hk : k≤blockLength lam X) :
    unorderedWeight tau lam k f X M=
      finiteSubsetWeight tau f X M (blockLength lam X) (blockLength lam X+1) Finset.univ := by
  exact (finiteSubsetWeight_eq_unordered_levels hf hk).symm

noncomputable def restrictedUnorderedBlock {n : ℕ} (X h a : ℕ)
    (F : (Fin n → ℝ) → ℝ) (B : Finset (Fin h)) (m : ℕ) : ℝ :=
  ∑ S : {S : Finset (Fin h) // S.card=n},
    if S.val⊆B then divisorSum X F m (fun i => a+(subsetEnumeration S i:ℕ)) else 0

noncomputable def restrictedBlock {n : ℕ} (X h a : ℕ)
    (F : (Fin n → ℝ) → ℝ) (A : Setoid (Fin n) → ℝ) (B : Finset (Fin h)) (m : ℕ) : ℝ :=
  ∑ b : Fin n → Fin h,A (Setoid.ker b)*
    (if ∀ i,b i∈B then divisorSum X F m (fun i => a+(b i:ℕ)) else 0)

theorem enumeratePerm_subset_iff {h n : ℕ}
    (S : {S : Finset (Fin h) // S.card=n}) (e : Equiv.Perm (Fin n)) (B : Finset (Fin h)) :
    (∀ i,(enumeratePerm (S,e)).val i∈B) ↔ S.val⊆B := by
  constructor
  · intro hi x hx
    rw [←enumeratePerm_image (S,e)] at hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact hi i
  · intro hS i
    apply hS
    rw [←enumeratePerm_image (S,e)]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩

theorem restrictedBlock_eq_unordered {n X h a m : ℕ} (hX : 2≤X)
    (F : (Fin n → ℝ) → ℝ) (B : Finset (Fin h))
    (hsym : ∀ (e : Equiv.Perm (Fin n)) v,(∀ i,0≤v i) → F (v ∘ e)=F v) :
    restrictedBlock X h a F (subsetCoefficient n) B m=restrictedUnorderedBlock X h a F B m := by
  classical
  unfold restrictedBlock
  have he : (∑ b : Fin n → Fin h,subsetCoefficient n (Setoid.ker b)*
      (if ∀ i,b i∈B then divisorSum X F m (fun i => a+(b i:ℕ)) else 0))=
      ∑ b : {b : Fin n → Fin h // Function.Injective b},
        (n.factorial:ℝ)⁻¹*(if ∀ i,b.val i∈B then divisorSum X F m (fun i => a+(b.val i:ℕ)) else 0) := by
    simp only [subsetCoefficient,Setoid.ker_eq_bot_iff,ite_mul,zero_mul]
    rw [←Finset.sum_filter]
    exact Finset.sum_subtype (p:=fun b : Fin n → Fin h => Function.Injective b)
      (Finset.univ.filter fun b : Fin n → Fin h => Function.Injective b) (by simp) _
  rw [he]
  rw [←Fintype.sum_equiv (Equiv.ofBijective enumeratePerm (enumeratePerm_bijective h n))
    (fun t => (n.factorial:ℝ)⁻¹*(if ∀ i,(enumeratePerm t).val i∈B then
      divisorSum X F m (fun i => a+((enumeratePerm t).val i:ℕ)) else 0)) _ (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  unfold restrictedUnorderedBlock
  apply Finset.sum_congr rfl
  intro S _
  have hd (e : Equiv.Perm (Fin n)) :
      divisorSum X F m (fun i => a+((enumeratePerm (S,e)).val i:ℕ))=
      divisorSum X F m (fun i => a+(subsetEnumeration S i:ℕ)) :=
    divisorSum_perm_orthant hX F hsym e (fun i => a+(subsetEnumeration S i:ℕ))
  simp only [hd,enumeratePerm_subset_iff,Finset.sum_const,Finset.card_univ,Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul]
  have hn : (n.factorial:ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [←mul_assoc, mul_inv_cancel₀ hn,one_mul]

theorem setDivisor_subset_level_sum (X M h a n : ℕ)
    (F : (j : ℕ) → (Fin j → ℝ) → ℝ) (B : Finset (Fin h)) :
    (∑ S ∈ Finset.powersetCard n (Finset.univ : Finset (Fin h)),
      if S⊆B then setDivisor F X M h a S else 0)=
      restrictedUnorderedBlock X h a (F n) B M := by
  classical
  rw [Finset.sum_subtype (p:=fun S : Finset (Fin h) => S.card=n)
    (Finset.powersetCard n Finset.univ) (by intro S; simp)]
  unfold restrictedUnorderedBlock
  apply Finset.sum_congr rfl
  intro S _
  rw [setDivisor_fixed_card F S.val S.property]

@[simp] theorem restrictedUnorderedBlock_zero (X h a M n : ℕ) (B : Finset (Fin h)) :
    restrictedUnorderedBlock X h a (0 : (Fin n → ℝ) → ℝ) B M=0 := by
  simp [restrictedUnorderedBlock]

end LargePrimeGaps

end OAI
