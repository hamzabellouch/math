import Mathlib
import OAI.Combinatorics.KMedianRecovery.Geometry.RoundingArithmetic
import OAI.Combinatorics.KMedianRecovery.Strictness.SortedDual
import OAI.Combinatorics.KMedianRecovery.Recovery.InitialProject
import OAI.Combinatorics.KMedianRecovery.Geometry.LocalRefineMachine

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
variable {m d : ℕ}
def pack (distance : Fin m→Fin d→ℚ) (F S : Finset (Fin m)) (k : ℕ) : List Bool :=
  encode [Rectangular.encode distance,List.replicate d true,BinaryFinSet.encode F,BinaryFinSet.encode S,k.bits]
noncomputable def target (x : List Bool) : List Bool :=
  (max (value (field 4 x)) (value (lengthBits (field 3 x)))).bits
noncomputable def target_computes : PolyComputes target :=
  NatOps.max (field_computes 4) ((field_computes 3).comp lengthBits_computes)
noncomputable def padded (x : List Bool) : List Bool :=
  BinaryCompletionPad.run (encode [field 2 x,field 3 x,target x])
noncomputable def padded_computes : PolyComputes padded :=
  (cons_computes (field_computes 2) (cons_computes (field_computes 3)
    (cons_computes target_computes (const_computes [])))).comp BinaryCompletionPad.run_computes
noncomputable def localInput (x : List Bool) : List Bool :=
  encode [field 0 x,field 1 x,map BinaryProjection.originalWord (field 2 x),BinaryProjection.lift (padded x)]
noncomputable def localInput_computes : PolyComputes localInput := by
  unfold localInput
  simpa only [Function.comp_def,encode] using
    cons_computes (field_computes 0) (cons_computes (field_computes 1)
      (cons_computes ((field_computes 2).comp (map_computes BinaryProjection.originalWord_computes))
        (cons_computes (padded_computes.comp BinaryProjection.lift_computes) (const_computes []))))
noncomputable def run : List Bool→List Bool := BinaryProjection.run ∘ BinaryLocalRefine.run ∘ localInput
noncomputable def run_computes : PolyComputes run := by
  unfold run
  simpa only [Function.comp_def] using
    localInput_computes.comp (BinaryLocalRefine.run_computes.comp BinaryProjection.run_computes)
lemma target_pack (distance : Fin m→Fin d→ℚ) (F S : Finset (Fin m)) (k : ℕ) :
    target (pack distance F S k)=(max k S.card).bits := by
  simp only [target,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryFinSet.encode,BinaryNatSet.encode,BinaryNatSet.pack,lengthBits_encode,value_bits,List.length_map,
    Finset.length_sort,BinaryFinSet.values_card]
lemma padded_pack (distance : Fin m→Fin d→ℚ) (F S : Finset (Fin m)) (k : ℕ) :
    padded (pack distance F S k)=BinaryFinSet.encode (Completion.Canonical.pad F S (max k S.card)) := by
  rw [padded,target_pack]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  exact BinaryFinSet.pad_pack F S _
lemma localInput_pack (distance : Fin m→Fin d→ℚ) (F S : Finset (Fin m)) (k : ℕ) :
    localInput (pack distance F S k)=BinaryLocalRefine.pack distance (F.sort (·≤·))
      (Completion.Canonical.pad F S (max k S.card)) := by
  have mapped : map BinaryProjection.originalWord (BinaryFinSet.encode F)=
      labels ((F.sort (·≤·)).map original) := by
    rw [BinaryFinSet.encode_eq,map_encode,List.map_map]
    simp only [labels,List.map_map]
    rfl
  rw [localInput,padded_pack,BinaryProjection.lift_encode]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryLocalRefine.pack,BinaryLocalSearch.pack]
  rw [mapped]
lemma integral_spec [MetricSpace (Fin m)] (δ : Fin m→Fin m→ℕ) (loc : Fin d→Fin m)
    (hloc : Function.Injective loc) (F S : Finset (Fin m)) (k : ℕ) (hSF : S⊆F) (hS : S.Nonempty)
    (hkF : k≤F.card) (hδ : ∀ j,∀ i∈F,(δ (loc j) i:ℝ)=dist (loc j) i)
    (hM : ∀ j,∀ i∈F,δ (loc j) i≤Rounding.cap d (IntegralAssembly.gamma/16)) :
    ∃ T : Finset (Fin m),run (pack (fun i j=>(δ (loc j) i:ℚ)) F S k)=BinaryFinSet.encode T ∧
      T⊆F ∧ T.Nonempty ∧ T.card=max k S.card ∧
      LocalSearch.cost (Finset.univ.image loc) T≤LocalSearch.cost (Finset.univ.image loc) S ∧
      LocalSearch.WidthLocalMin F (Finset.univ.image loc) T 5 := by
  let U:=Completion.Canonical.pad F S (max k S.card)
  have hUF : U⊆F := Completion.Canonical.pad_subset F S _ hSF
  have hSU : S⊆U := Completion.Canonical.subset_pad F S _
  have hU : U.Nonempty := hS.mono hSU
  have hcard : U.card=max k S.card :=
    Completion.Canonical.pad_card F S _ hSF (le_max_right _ _) (max_le hkF (Finset.card_le_card hSF))
  obtain ⟨T,he,hTF,hT,hTc,hcost,hmin⟩:=BinaryLocalRefine.integral_spec δ loc hloc (F.sort (·≤·)) U
    (by simpa only [Finset.sort_toFinset] using hUF) hU
    (by simpa only [Finset.sort_toFinset] using hδ) (by simpa only [Finset.sort_toFinset] using hM)
  refine ⟨T,?_,by simpa only [Finset.sort_toFinset] using hTF,hT,hTc.trans hcard,
    hcost.trans (LocalSearch.cost_mono _ hS hSU),by simpa only [Finset.sort_toFinset] using hmin⟩
  rw [run,Function.comp_apply,Function.comp_apply,localInput_pack,he,BinaryProjection.run_setBits]
  congr 1
  simp only [RationalLeaves.project,Finset.image_image]
  change T.image id=T
  exact Finset.image_id
end MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess

namespace MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
variable {m : ℕ}
def pack (δ : Fin m→Fin m→ℕ) (F D : Finset (Fin m)) (M h L : ℕ) : List Bool :=
  pairBits (BinaryInitialAuto.pack (fun i j=>(δ (SortedIndex.enum D j) i:ℚ))
    (SortedIndex.enum D) F (M:ℚ) h,(h+L).bits)
noncomputable def postInput (v : ℚ) (C : ℕ) (x : List Bool) : List Bool :=
  encode [field 0 (extractPrefix x),field 1 (extractPrefix x),field 2 (extractPrefix x),
    BinaryInitialProject.run v C (extractPrefix x),discardPrefix x]
noncomputable def postInput_computes (v : ℚ) (C : ℕ) : PolyComputes (postInput v C) := by
  unfold postInput
  simpa only [Function.comp_def,encode] using
    cons_computes (extractPrefix_computes.comp (field_computes 0))
      (cons_computes (extractPrefix_computes.comp (field_computes 1))
        (cons_computes (extractPrefix_computes.comp (field_computes 2))
          (cons_computes (extractPrefix_computes.comp (BinaryInitialProject.run_computes v C))
            (cons_computes discardPrefix_computes (const_computes [])))))
noncomputable def run (v : ℚ) (C : ℕ) : List Bool→List Bool := BinarySurplusPostprocess.run ∘ postInput v C
noncomputable def run_computes (v : ℚ) (C : ℕ) : PolyComputes (run v C) :=
  (postInput_computes v C).comp BinarySurplusPostprocess.run_computes
lemma produce [MetricSpace (Fin m)] (δ : Fin m→Fin m→ℕ) (F D : Finset (Fin m))
    (h L M N C : ℕ) (v : ℚ) (hD : D.Nonempty) (hh : 2≤h) (hkF : h+L≤F.card)
    (hN : N=D.card+F.card) (hM : 0<M)
    (hδ : ∀ p∈D,∀ i∈F,(δ p i:ℝ)=dist p i)
    (hmetric : ∀ i j,(δ (SortedIndex.enum D j) i:ℝ)=dist i (SortedIndex.enum D j))
    (hfar : ∀ i∈F,∀ p∈D,1≤dist i p)
    (hdiam : ∀ p∈D,∀ i∈F,δ p i≤M)
    (hcap : ∀ p∈D,∀ i∈F,δ p i≤Rounding.cap D.card (IntegralAssembly.gamma/16))
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)≤1/12)
    (hvc : (v:ℝ)≤ strictnessGap (200*Anchoring.countConstant (1/100))/1000)
    (hsmall : (v:ℝ)^2≤ strictnessGap (200*Anchoring.countConstant (1/100))/(6*(200*Anchoring.countConstant (1/100)+2)))
    (hsize : 2/(N:ℝ)≤ strictnessGap (200*Anchoring.countConstant (1/100))/200)
    (herror : (N:ℝ)^2/2^N≤(v:ℝ))
    (hL : 3*(HistoryPhaseBound.limit v ((M:ℝ)+8*(D.card:ℝ)*(M:ℝ))+1)≤L)
    (hC : 2≤(1+v^2)^C) :
    ∃ S : Finset (Fin m),run v C (pack δ F D M h L)=BinaryFinSet.encode S ∧
      S⊆F ∧ S.Nonempty ∧ S.card=h+L ∧ LocalSearch.WidthLocalMin F D S 5 ∧
      ∀ O H : Finset (Fin m),∀ xi : ℝ,
        O⊆F→O.card=h→H⊆F→H.Nonempty→H.card+L=h→
        LocalSearch.cost D H≤(1+xi)*LocalSearch.cost D O→xi≤1→
        LocalSearch.cost D S≤(2-strictnessGap (200*Anchoring.countConstant (1/100))/100)*LocalSearch.cost D O := by
  classical
  have hn : 0<D.card := Finset.card_pos.mpr hD
  have hnN : D.card≤N := by omega
  have hhN : h≤N := by omega
  have hN3 : 3≤N := by omega
  have hF : F.Nonempty := Finset.card_pos.mp (by omega)
  have hfar' (i : Fin m) (hi : i∈F) (j : Fin D.card) : 1≤dist i (SortedIndex.enum D j) :=
    hfar i hi _ (SortedIndex.enum_mem D j)
  have hdiam' (i : Fin m) (hi : i∈F) (j : Fin D.card) : dist i (SortedIndex.enum D j)≤((M:ℚ):ℝ) := by
    rw [←hmetric]
    exact_mod_cast hdiam _ (SortedIndex.enum_mem D j) i hi
  have hNQ : (1:ℚ)≤N := by exact_mod_cast (by omega : 1≤N)
  have hnQ : (1:ℚ)≤D.card := by exact_mod_cast hn
  have hMQ : (1:ℚ)≤M := by exact_mod_cast hM
  have hlo : (0:ℚ)<2/(N:ℚ)^2 := by positivity
  have hlohi : 2/(N:ℚ)^2≤8*(D.card:ℚ)*(M:ℚ) := by
    have htwo : 2/(N:ℚ)^2≤2 := by
      apply (div_le_iff₀ (sq_pos_of_pos (by linarith : (0:ℚ)<N))).mpr
      nlinarith only [hNQ]
    have hprod : (1:ℚ)≤(D.card:ℚ)*(M:ℚ) := by
      simpa only [one_mul] using mul_le_mul hnQ hMQ (by norm_num : (0:ℚ)≤1) (by linarith : (0:ℚ)≤D.card)
    linarith only [htwo,hprod]
  let distance : Fin m→Fin D.card→ℚ := fun i j=>(δ (SortedIndex.enum D j) i:ℚ)
  let U := (start (SortedIndex.enum D) distance F v (2/(N:ℚ)^2) M N N
    (HistoryPhaseBound.limit v ((M:ℝ)+8*(D.card:ℝ)*M)+1) h).project
  have hdistance (i : Fin m) (j : Fin D.card) : (distance i j:ℝ)=dist i (SortedIndex.enum D j) := by
    simpa only [distance,Rat.cast_natCast] using hmetric i j
  have hrate : 0≤(1:ℝ)/2^N := by positivity
  have hcert := start_certificate (SortedIndex.enum D) distance hdistance F v (2/(N:ℚ)^2) M
    ((1:ℝ)/2^N) N N h hn hnN hh hF (by exact_mod_cast hM) hN3 hv
    (by linarith only [hv1]) hlo hrate hlohi
    (by simp only [Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat,le_refl]) hfar' hdiam'
  simp only [Rat.cast_natCast] at hcert
  change LowCertificate (SortedIndex.enum D) F U v ((2/(N:ℚ)^2:ℚ):ℝ) h ∨
    NormalCertificate (SortedIndex.enum D) F U v ((2/(N:ℚ)^2:ℚ):ℝ) (8*(D.card:ℝ)*M) ((1:ℝ)/2^N)
      (HistoryPhaseBound.limit v ((M:ℝ)+8*(D.card:ℝ)*M)+1) h at hcert
  have hinit : BinaryInitialProject.run v C
      (BinaryInitialAuto.pack distance (SortedIndex.enum D) F (M:ℚ) h)=BinaryFinSet.encode U := by
    simpa only [←hN,U,Rat.cast_natCast] using BinaryInitialProject.run_pack distance (SortedIndex.enum D) hdistance F v M C h
      (by exact_mod_cast hv) hC hn hh hF (by exact_mod_cast hM) (by omega)
      (by linarith only [hv1]) (by simpa only [←hN] using hlohi) hfar' hdiam'
  have hpost : postInput v C (pack δ F D M h L)=BinarySurplusPostprocess.pack distance F U (h+L) := by
    simp only [postInput,pack,extractPrefix_pairBits,discardPrefix_pairBits]
    change encode [field 0 (BinaryInitialAuto.pack distance (SortedIndex.enum D) F M h),
      field 1 (BinaryInitialAuto.pack distance (SortedIndex.enum D) F M h),
      field 2 (BinaryInitialAuto.pack distance (SortedIndex.enum D) F M h),
      BinaryInitialProject.run v C (BinaryInitialAuto.pack distance (SortedIndex.enum D) F M h),(h+L).bits]=_
    rw [hinit]
    simp only [BinaryInitialAuto.pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
      Option.getD_some,BinarySurplusPostprocess.pack]
  have hUdata : U⊆F ∧ U.Nonempty ∧ U.card≤h+L := by
    rcases hcert with hc|hc
    · exact ⟨hc.1,hc.2.1,hc.2.2.1.trans (by omega)⟩
    · exact ⟨hc.1,hc.2.1,hc.2.2.1.trans (by omega)⟩
  obtain ⟨S,he,hSF,hS,hSc,hSU,hlocal⟩ := BinarySurplusPostprocess.integral_spec δ (SortedIndex.enum D)
    (SortedIndex.enum_injective D) F U (h+L) hUdata.1 hUdata.2.1 hkF
    (fun j i hi=>hδ _ (SortedIndex.enum_mem D j) i hi)
    (fun j i hi=>hcap _ (SortedIndex.enum_mem D j) i hi)
  rw [SortedIndex.image_enum] at hSU hlocal
  rw [max_eq_left hUdata.2.2] at hSc
  refine ⟨S,?_,hSF,hS,hSc,hlocal,?_⟩
  · rw [run,Function.comp_apply,hpost]
    exact he
  intro O H xi hOF hOh hHF hH hHL hHcost hxi
  have hO : O.Nonempty := Finset.card_pos.mp (by omega)
  rcases hcert with hc|hc
  · obtain ⟨_,_,_,Q,alpha,hQ,hcost,hdual,hpay⟩ := hc
    rw [SortedIndex.sum_cost] at hcost
    have hd := SortedIndex.dual_on_points D F v ((2/(N:ℚ)^2:ℚ):ℝ) alpha hdual
    have hp : (1-3*(v:ℝ))*Q≤∑ j:D,(alpha ∘ (SortedIndex.equiv_dual D).symm) j := by
      rw [SortedIndex.sum_budget]
      exact hpay
    have hd' : PhaseOriginalLedger.Dual (fun j:D=>j.val) F v (2/(N:ℝ)^2)
        (alpha ∘ (SortedIndex.equiv_dual D).symm) := by
      simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_pow,Rat.cast_natCast] using hd
    exact PhaseSurplusProducer.small_cost F D O S hO hD hOF hfar N (by omega) (by omega)
      _ Q v hd' (hSU.trans hcost) hv hv1 hvc hsmall hsize hp
  · obtain ⟨_,_,_,lam,Q,alpha,hlo',_,hQ,hcost,hdual,hpay⟩ := hc
    rw [SortedIndex.sum_cost] at hcost
    have hd := SortedIndex.dual_on_points D F v lam alpha hdual
    have hlam : 0<lam := (Rat.cast_pos.mpr hlo).trans_le hlo'
    have hP1 := PhaseSurplusProducer.comparison_ge_one F D O hD hO hOF hfar
    have hOe : (O.card:ℝ)≤N := by exact_mod_cast (by omega : O.card≤N)
    have hne : (D.card:ℝ)≤N := by exact_mod_cast hnN
    have hprod : (O.card:ℝ)*D.card≤(N:ℝ)^2 := by
      simpa only [pow_two] using mul_le_mul hOe hne (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have herr : (O.card:ℝ)*D.card*((1:ℝ)/2^N)≤(v:ℝ)*LocalSearch.cost D O := by
      calc
        _≤(N:ℝ)^2*((1:ℝ)/2^N) := mul_le_mul_of_nonneg_right hprod hrate
        _=(N:ℝ)^2/2^N := by ring
        _≤(v:ℝ) := herror
        _≤(v:ℝ)*LocalSearch.cost D O := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hP1 hv.le
    have hp : (1-3*(v:ℝ))*Q+(O.card:ℝ)*(lam-(D.card:ℝ)*((1:ℝ)/2^N))≤
        ∑ j:D,(alpha ∘ (SortedIndex.equiv_dual D).symm) j := by
      rw [SortedIndex.sum_budget,hOh]
      exact hpay
    exact PhaseSurplusProducer.normal_cost F D O S H hO hS hH hOF hSF hHF (by omega) L (by omega)
      (by omega) hlocal (by linarith only [hP1]) _ lam Q ((1:ℝ)/2^N) xi v hd hlam hQ
      (hSU.trans hcost) hHcost hxi hv hv1 hvc hsmall herr hp
end MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus

end OAI
