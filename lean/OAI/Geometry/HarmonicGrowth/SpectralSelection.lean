import OAI.Geometry.HarmonicGrowth.HopfSpectrum

namespace OAI

noncomputable section


namespace HarmonicCounterexample.Construction
open Module Angular LinearODE Certificate
open scoped BigOperators

lemma charge_distinct {l p q:ℕ} (hp:2*p<l+2) (hq:2*q<l+2)
    (h:(-((p:ℝ)-(l+2-p:ℕ))^2)=(-((q:ℝ)-(l+2-q:ℕ))^2)) : p=q := by
  have hpl : p≤l+2 := by omega
  have hql : q≤l+2 := by omega
  rw [Nat.cast_sub hpl,Nat.cast_sub hql] at h
  have hp' : 2*(p:ℝ)<(l+2:ℕ) := by exact_mod_cast hp
  have hq' : 2*(q:ℝ)<(l+2:ℕ) := by exact_mod_cast hq
  have he : (p:ℝ)=q := by nlinarith
  exact_mod_cast he

lemma exists_charge_prefix (l b:ℕ) (hb:2*b<l+2) :
    ∃ s:Finset (Index l),
      (s.card:ℚ)=2*(((l+2:ℕ):ℚ)+7)/7*countPrefix ((l+2:ℕ):ℚ) b ∧
      (∑i∈s,d0 l i)=-(2*(((l+2:ℕ):ℚ)+7)/7*chargePrefix ((l+2:ℕ):ℚ) b:ℚ) := by
  classical
  have hp (p:Fin (b+1)) : p.val≤l+2 := by have := p.isLt;omega
  have hpm (p:Fin (b+1)) : p.val≠l+2-p.val := by have := p.isLt;omega
  have hex (p:Fin (b+1)) : ∃s:Finset (Index l),
      s⊆({i | d0 l i= -((p.val:ℝ)-(l+2-p.val:ℕ))^2}:Finset (Index l)) ∧
      s.card=2*hopfMultiplicity p.val (l+2-p.val) :=
    Finset.exists_subset_card_eq
      (eigen_multiplicity l p.val (l+2-p.val) (by have := hp p;omega) (hpm p))
  choose S hS hcard using hex
  have hd : ((Finset.univ:Finset (Fin (b+1))):Set (Fin (b+1))).PairwiseDisjoint S := by
    intro p _ q _ hpq
    apply Finset.disjoint_left.mpr
    intro i hip hiq
    have he : p.val=q.val := charge_distinct (by have := p.isLt;omega)
      (by have := q.isLt;omega)
      ((Finset.mem_filter.mp (hS p hip)).2.symm.trans (Finset.mem_filter.mp (hS q hiq)).2)
    exact hpq (Fin.ext he)
  refine ⟨Finset.univ.biUnion S,?_,?_⟩
  · rw [Finset.card_biUnion hd,Nat.cast_sum]
    simp only [hcard,Nat.cast_mul,Nat.cast_ofNat]
    have he := pairMultiplicity_sum (l+2) b
    rw [← Fin.sum_univ_eq_sum_range] at he
    simp_rw [pairMultiplicity_eq (hp _)] at he
    exact he
  · rw [Finset.sum_biUnion hd]
    have hc : ∀p:Fin (b+1),(∑i∈S p,d0 l i)=
        -(2*(hopfMultiplicity p.val (l+2-p.val):ℝ))*(((l+2:ℕ):ℝ)-2*p.val)^2 := by
      intro p
      rw [Finset.sum_congr rfl (fun i hi=>(Finset.mem_filter.mp (hS p hi)).2),
        Finset.sum_const,hcard,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sub (hp p)]
      ring
    simp_rw [hc]
    have he := pairMultiplicity_charge_sum (l+2) b
    rw [← Fin.sum_univ_eq_sum_range] at he
    simp_rw [pairMultiplicity_eq (hp _)] at he
    have her : (∑p:Fin (b+1),2*(hopfMultiplicity p.val (l+2-p.val):ℝ)*
        (((l+2:ℕ):ℝ)-2*p.val)^2)=
        ((2*(((l+2:ℕ):ℚ)+7)/7*chargePrefix ((l+2:ℕ):ℚ) b:ℚ):ℝ) := by
      exact_mod_cast he
    rw [← her,← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p _;ring

lemma exists_selected_group (g:GroupCertificate) :
    ∃s:Finset (Index (g.degree-2)),s.card=g.count ∧
      (∑i∈s,root (g.degree-2) i)<50000*(s.card:ℝ) := by
  have hl : g.degree-2+2=g.degree := by have := g.degree_ge;omega
  obtain ⟨s,hc,hd⟩ := exists_charge_prefix (g.degree-2) g.bound (by rw [hl];exact g.nonmiddle)
  rw [hl,g.count_exact] at hc
  rw [hl,g.charge_exact] at hd
  have hcn : s.card=g.count := by exact_mod_cast hc
  refine ⟨s,hcn,mean_root_from_lambda s ?_⟩
  simp only [lambda_exact]
  rw [← Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,hd,hcn]
  have hB : B (g.degree-2)=(g.degree:ℝ)*(g.degree+14) := by
    unfold B degree
    have he : ((g.degree-2:ℕ):ℝ)+2=g.degree := by exact_mod_cast hl
    rw [he]
  rw [hB]
  have hm : 100000*(101*(g.degree:ℝ)*(g.degree+14)*g.count-g.charge)<
      101*99853*50000*(50000+14)*g.count := by exact_mod_cast g.strict_margin
  push_cast
  nlinarith

end HarmonicCounterexample.Construction

end

noncomputable section


namespace HarmonicCounterexample.Certificate
open scoped BigOperators

lemma block0_degrees : (block0.map GroupCertificate.degree)=List.range' 49964 10 := by
  norm_num [block0,group49964,group49965,group49966,group49967,group49968,group49969,group49970,group49971,group49972,group49973,List.range']

lemma block1_degrees : (block1.map GroupCertificate.degree)=List.range' 49974 10 := by
  norm_num [block1,group49974,group49975,group49976,group49977,group49978,group49979,group49980,group49981,group49982,group49983,List.range']

lemma block2_degrees : (block2.map GroupCertificate.degree)=List.range' 49984 10 := by
  norm_num [block2,group49984,group49985,group49986,group49987,group49988,group49989,group49990,group49991,group49992,group49993,List.range']

lemma block3_degrees : (block3.map GroupCertificate.degree)=List.range' 49994 10 := by
  norm_num [block3,group49994,group49995,group49996,group49997,group49998,group49999,group50000,group50001,group50002,group50003,List.range']

lemma block4_degrees : (block4.map GroupCertificate.degree)=List.range' 50004 10 := by
  norm_num [block4,group50004,group50005,group50006,group50007,group50008,group50009,group50010,group50011,group50012,group50013,List.range']

lemma block5_degrees : (block5.map GroupCertificate.degree)=List.range' 50014 10 := by
  norm_num [block5,group50014,group50015,group50016,group50017,group50018,group50019,group50020,group50021,group50022,group50023,List.range']

lemma block6_degrees : (block6.map GroupCertificate.degree)=List.range' 50024 10 := by
  norm_num [block6,group50024,group50025,group50026,group50027,group50028,group50029,group50030,group50031,group50032,group50033,List.range']

lemma block7_degrees : (block7.map GroupCertificate.degree)=List.range' 50034 10 := by
  norm_num [block7,group50034,group50035,group50036,group50037,group50038,group50039,group50040,group50041,group50042,group50043,List.range']

lemma block8_degrees : (block8.map GroupCertificate.degree)=List.range' 50044 10 := by
  norm_num [block8,group50044,group50045,group50046,group50047,group50048,group50049,group50050,group50051,group50052,group50053,List.range']

lemma block9_degrees : (block9.map GroupCertificate.degree)=List.range' 50054 10 := by
  norm_num [block9,group50054,group50055,group50056,group50057,group50058,group50059,group50060,group50061,group50062,group50063,List.range']

lemma block10_degrees : (block10.map GroupCertificate.degree)=List.range' 50064 10 := by
  norm_num [block10,group50064,group50065,group50066,group50067,group50068,group50069,group50070,group50071,group50072,group50073,List.range']

lemma block11_degrees : (block11.map GroupCertificate.degree)=List.range' 50074 10 := by
  norm_num [block11,group50074,group50075,group50076,group50077,group50078,group50079,group50080,group50081,group50082,group50083,List.range']

lemma block12_degrees : (block12.map GroupCertificate.degree)=List.range' 50084 10 := by
  norm_num [block12,group50084,group50085,group50086,group50087,group50088,group50089,group50090,group50091,group50092,group50093,List.range']

lemma block13_degrees : (block13.map GroupCertificate.degree)=List.range' 50094 10 := by
  norm_num [block13,group50094,group50095,group50096,group50097,group50098,group50099,group50100,group50101,group50102,group50103,List.range']

lemma block14_degrees : (block14.map GroupCertificate.degree)=List.range' 50104 10 := by
  norm_num [block14,group50104,group50105,group50106,group50107,group50108,group50109,group50110,group50111,group50112,group50113,List.range']

lemma block15_degrees : (block15.map GroupCertificate.degree)=List.range' 50114 10 := by
  norm_num [block15,group50114,group50115,group50116,group50117,group50118,group50119,group50120,group50121,group50122,group50123,List.range']

lemma block16_degrees : (block16.map GroupCertificate.degree)=List.range' 50124 10 := by
  norm_num [block16,group50124,group50125,group50126,group50127,group50128,group50129,group50130,group50131,group50132,group50133,List.range']

lemma block17_degrees : (block17.map GroupCertificate.degree)=List.range' 50134 10 := by
  norm_num [block17,group50134,group50135,group50136,group50137,group50138,group50139,group50140,group50141,group50142,group50143,List.range']

lemma block18_degrees : (block18.map GroupCertificate.degree)=List.range' 50144 10 := by
  norm_num [block18,group50144,group50145,group50146,group50147,group50148,group50149,group50150,group50151,group50152,group50153,List.range']

lemma block19_degrees : (block19.map GroupCertificate.degree)=List.range' 50154 10 := by
  norm_num [block19,group50154,group50155,group50156,group50157,group50158,group50159,group50160,group50161,group50162,group50163,List.range']

lemma block20_degrees : (block20.map GroupCertificate.degree)=List.range' 50164 10 := by
  norm_num [block20,group50164,group50165,group50166,group50167,group50168,group50169,group50170,group50171,group50172,group50173,List.range']

lemma block21_degrees : (block21.map GroupCertificate.degree)=List.range' 50174 10 := by
  norm_num [block21,group50174,group50175,group50176,group50177,group50178,group50179,group50180,group50181,group50182,group50183,List.range']

lemma block22_degrees : (block22.map GroupCertificate.degree)=List.range' 50184 10 := by
  norm_num [block22,group50184,group50185,group50186,group50187,group50188,group50189,group50190,group50191,group50192,group50193,List.range']

lemma block23_degrees : (block23.map GroupCertificate.degree)=List.range' 50194 10 := by
  norm_num [block23,group50194,group50195,group50196,group50197,group50198,group50199,group50200,group50201,group50202,group50203,List.range']

lemma block24_degrees : (block24.map GroupCertificate.degree)=List.range' 50204 9 := by
  norm_num [block24,group50204,group50205,group50206,group50207,group50208,group50209,group50210,group50211,group50212,List.range']

lemma superblock0_degrees : (superblock0.map GroupCertificate.degree)=List.range' 49964 50 := by
  simp only [superblock0,List.map_append,block0_degrees,block1_degrees,block2_degrees,block3_degrees,block4_degrees]
  rw [show List.range' 49964 10 ++ List.range' 49974 10 = List.range' 49964 20 from List.range'_append_1]
  rw [show List.range' 49964 20 ++ List.range' 49984 10 = List.range' 49964 30 from List.range'_append_1]
  rw [show List.range' 49964 30 ++ List.range' 49994 10 = List.range' 49964 40 from List.range'_append_1]
  rw [show List.range' 49964 40 ++ List.range' 50004 10 = List.range' 49964 50 from List.range'_append_1]

lemma superblock1_degrees : (superblock1.map GroupCertificate.degree)=List.range' 50014 50 := by
  simp only [superblock1,List.map_append,block5_degrees,block6_degrees,block7_degrees,block8_degrees,block9_degrees]
  rw [show List.range' 50014 10 ++ List.range' 50024 10 = List.range' 50014 20 from List.range'_append_1]
  rw [show List.range' 50014 20 ++ List.range' 50034 10 = List.range' 50014 30 from List.range'_append_1]
  rw [show List.range' 50014 30 ++ List.range' 50044 10 = List.range' 50014 40 from List.range'_append_1]
  rw [show List.range' 50014 40 ++ List.range' 50054 10 = List.range' 50014 50 from List.range'_append_1]

lemma superblock2_degrees : (superblock2.map GroupCertificate.degree)=List.range' 50064 50 := by
  simp only [superblock2,List.map_append,block10_degrees,block11_degrees,block12_degrees,block13_degrees,block14_degrees]
  rw [show List.range' 50064 10 ++ List.range' 50074 10 = List.range' 50064 20 from List.range'_append_1]
  rw [show List.range' 50064 20 ++ List.range' 50084 10 = List.range' 50064 30 from List.range'_append_1]
  rw [show List.range' 50064 30 ++ List.range' 50094 10 = List.range' 50064 40 from List.range'_append_1]
  rw [show List.range' 50064 40 ++ List.range' 50104 10 = List.range' 50064 50 from List.range'_append_1]

lemma superblock3_degrees : (superblock3.map GroupCertificate.degree)=List.range' 50114 50 := by
  simp only [superblock3,List.map_append,block15_degrees,block16_degrees,block17_degrees,block18_degrees,block19_degrees]
  rw [show List.range' 50114 10 ++ List.range' 50124 10 = List.range' 50114 20 from List.range'_append_1]
  rw [show List.range' 50114 20 ++ List.range' 50134 10 = List.range' 50114 30 from List.range'_append_1]
  rw [show List.range' 50114 30 ++ List.range' 50144 10 = List.range' 50114 40 from List.range'_append_1]
  rw [show List.range' 50114 40 ++ List.range' 50154 10 = List.range' 50114 50 from List.range'_append_1]

lemma superblock4_degrees : (superblock4.map GroupCertificate.degree)=List.range' 50164 49 := by
  simp only [superblock4,List.map_append,block20_degrees,block21_degrees,block22_degrees,block23_degrees,block24_degrees]
  rw [show List.range' 50164 10 ++ List.range' 50174 10 = List.range' 50164 20 from List.range'_append_1]
  rw [show List.range' 50164 20 ++ List.range' 50184 10 = List.range' 50164 30 from List.range'_append_1]
  rw [show List.range' 50164 30 ++ List.range' 50194 10 = List.range' 50164 40 from List.range'_append_1]
  rw [show List.range' 50164 40 ++ List.range' 50204 9 = List.range' 50164 49 from List.range'_append_1]

lemma selectedGroups_degrees : (selectedGroups.map GroupCertificate.degree)=List.range' 49964 249 := by
  simp only [selectedGroups,List.map_append,superblock0_degrees,superblock1_degrees,
    superblock2_degrees,superblock3_degrees,superblock4_degrees]
  rw [show List.range' 49964 50 ++ List.range' 50014 50 = List.range' 49964 100 from List.range'_append_1]
  rw [show List.range' 49964 100 ++ List.range' 50064 50 = List.range' 49964 150 from List.range'_append_1]
  rw [show List.range' 49964 150 ++ List.range' 50114 50 = List.range' 49964 200 from List.range'_append_1]
  rw [show List.range' 49964 200 ++ List.range' 50164 49 = List.range' 49964 249 from List.range'_append_1]

lemma selectedGroups_length : selectedGroups.length=249 := by
  have h:=congrArg List.length selectedGroups_degrees
  simpa only [List.length_map,List.length_range'] using h

def selectedGroup (i:Fin 249) : GroupCertificate :=
  selectedGroups[i.val]'(by rw [selectedGroups_length];exact i.isLt)

lemma selectedGroup_degree (i:Fin 249) : (selectedGroup i).degree=49964+i.val := by
  have h : i.val<(selectedGroups.map GroupCertificate.degree).length := by
    rw [List.length_map,selectedGroups_length];exact i.isLt
  have he := congrArg (fun l:List ℕ=>l[i.val]?) selectedGroups_degrees
  simp only [List.getElem?_eq_getElem h,List.getElem_map] at he
  have hr : i.val<(List.range' 49964 249).length := by simp
  rw [List.getElem?_eq_getElem hr,List.getElem_range'] at he
  simpa only [Nat.one_mul,Option.some.injEq,selectedGroup] using he

lemma list_sum_getElem {α:Type*} (l:List α) (N:ℕ) (h:l.length=N) (f:α→ℕ) :
    (∑i:Fin N,f (l[i.val]'(by rw [h];exact i.isLt)))=(l.map f).sum := by
  subst N
  rw [← List.sum_ofFn]
  congr 1
  change List.ofFn (f ∘ (fun i:Fin l.length=>l[i.val]))=List.map f l
  rw [← List.map_ofFn,List.ofFn_getElem]

lemma selectedGroup_count_sum : (∑i:Fin 249,(selectedGroup i).count)=
    (selectedGroups.map GroupCertificate.count).sum :=
  list_sum_getElem selectedGroups 249 selectedGroups_length GroupCertificate.count

end HarmonicCounterexample.Certificate

end

noncomputable section


namespace HarmonicCounterexample.Construction
open Module Angular LinearODE Certificate
open scoped BigOperators

abbrev L : ℕ := 49962+249

def selectionCountFormula (l:Fin L) : ℕ :=
  if h:l.val<49962 then Module.finrank ℝ (H l.val)
  else (selectedGroup ⟨l.val-49962,by have := l.isLt;unfold L at this;omega⟩).count

/-- The same finite count, packaged opaquely by choice to avoid evaluating the
249-entry certificate during kernel conversion of dependent finite sums. -/
def selectionCount : Fin L→ℕ :=
  Classical.choose (show ∃f:Fin L→ℕ,∀l,f l=selectionCountFormula l from ⟨selectionCountFormula,fun _=>rfl⟩)

lemma selectionCount_eq (l:Fin L) : selectionCount l=selectionCountFormula l :=
  (Classical.choose_spec (show ∃f:Fin L→ℕ,∀l,f l=selectionCountFormula l from ⟨selectionCountFormula,fun _=>rfl⟩)) l

lemma exists_selection (l:Fin L) : ∃s:Finset (Index l.val),s.card=selectionCount l ∧
    (∑i∈s,root l.val i)<50000*(s.card:ℝ) := by
  classical
  by_cases h:l.val<49962
  · refine ⟨Finset.univ,?_,?_⟩
    · simp only [selectionCount_eq,selectionCountFormula,dite_eq_left h,Finset.card_univ,Fintype.card_fin]
    · simpa only [Finset.card_univ] using full_mean_root (by omega : l.val+2≤49963)
  · let i:Fin 249 := ⟨l.val-49962,by have := l.isLt;unfold L at this;omega⟩
    have hd : (selectedGroup i).degree-2=l.val := by
      rw [selectedGroup_degree];dsimp only [i];omega
    have hs := exists_selected_group (selectedGroup i)
    rw [hd] at hs
    simpa only [selectionCount_eq,selectionCountFormula,dite_eq_right h] using hs

def selected (l:Fin L) : Finset (Index l.val) := Classical.choose (exists_selection l)
lemma selected_card (l:Fin L) : (selected l).card=selectionCount l :=
  (Classical.choose_spec (exists_selection l)).1
lemma selected_mean (l:Fin L) : (∑i∈selected l,root l.val i)<50000*((selected l).card:ℝ) :=
  (Classical.choose_spec (exists_selection l)).2
lemma selected_nonempty (l:Fin L) : (selected l).Nonempty := by
  by_contra h
  have he := Finset.not_nonempty_iff_eq_empty.mp h
  have hm := selected_mean l
  simp only [he,Finset.sum_empty,Finset.card_empty,Nat.cast_zero,mul_zero,lt_self_iff_false] at hm
instance selectionCount_nonzero (l:Fin L) : NeZero (selectionCount l) :=
  ⟨by rw [← selected_card];exact (selected_nonempty l).card_pos.ne'⟩

lemma dim_exact (l:ℕ) : Module.finrank ℝ (H l)=(l+16).choose 14+(l+15).choose 14 := by
  rw [← (Control.realCartesianHarmonic (l+2)).finrank_eq,
    ComplexAngular.realHarmonicSpace_finrank,ComplexAngular.harmonicSpace_finrank_sixteen]

lemma low_count_formula (m:ℕ) : (∑l∈Finset.range m,Module.finrank ℝ (H l))+17=
    (m+16).choose 15+(m+15).choose 15 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Finset.sum_range_succ,dim_exact]
    have h1 := Nat.choose_succ_succ (m+16) 14
    have h2 := Nat.choose_succ_succ (m+15) 14
    norm_num only [Nat.succ_eq_add_one,Nat.add_assoc] at h1 h2 ⊢
    omega


end HarmonicCounterexample.Construction

end

noncomputable section


namespace HarmonicCounterexample.Construction
open Certificate
open scoped BigOperators

lemma selectionCount_low (l:Fin 49962) : selectionCount (l.castAdd 249)=Module.finrank ℝ (H l.val) := by
  rw [selectionCount_eq,selectionCountFormula,dite_eq_left (by simp)]
  rfl

lemma selectionCount_high (i:Fin 249) : selectionCount (i.natAdd 49962)=(selectedGroup i).count := by
  rw [selectionCount_eq,selectionCountFormula,dite_eq_right (by simp only [Fin.val_natAdd];omega)]
  apply congrArg (fun i:Fin 249=>(selectedGroup i).count)
  apply Fin.ext
  simp only [Fin.val_natAdd,Nat.add_sub_cancel_left]


lemma fin_sum_blocks {n m:ℕ} (f:Fin (n+m)→ℕ) (a:Fin n→ℕ) (b:Fin m→ℕ)
    (ha:∀i,f (i.castAdd m)=a i) (hb:∀i,f (i.natAdd n)=b i) :
    (∑i,f i)=(∑i,a i)+(∑i,b i) := by
  rw [Fin.sum_univ_add]
  exact congrArg₂ Nat.add (Finset.sum_congr rfl (fun i _=>ha i))
    (Finset.sum_congr rfl (fun i _=>hb i))

lemma large_sum_blocks (f:Fin L→ℕ) (a:Fin 49962→ℕ) (b:Fin 249→ℕ)
    (ha:∀i,f (i.castAdd 249)=a i) (hb:∀i,f (i.natAdd 49962)=b i) :
    (∑i,f i)=(∑i,a i)+(∑i,b i) :=
  fin_sum_blocks (n:=49962) (m:=249) f a b ha hb

lemma large_raw_split (f:Fin L→ℕ) : (∑l:Fin L,f l)=
    (∑l:Fin 49962,f (l.castAdd 249))+(∑i:Fin 249,f (i.natAdd 49962)) :=
  large_sum_blocks f _ _ (fun _=>rfl) (fun _=>rfl)

lemma selectionCount_raw_split : (∑l:Fin L,selectionCount l)=
    (∑l:Fin 49962,selectionCount (l.castAdd 249))+(∑i:Fin 249,selectionCount (i.natAdd 49962)) :=
  large_raw_split selectionCount

lemma selectionCount_low_sum : (∑l:Fin 49962,selectionCount (l.castAdd 249))=
    ∑l:Fin 49962,Module.finrank ℝ (H l.val) :=
  Finset.sum_congr rfl (fun l _=>selectionCount_low l)

lemma selectionCount_high_sum : (∑i:Fin 249,selectionCount (i.natAdd 49962))=
    ∑i:Fin 249,(selectedGroup i).count :=
  Finset.sum_congr rfl (fun i _=>selectionCount_high i)

lemma selectionCount_split : (∑l:Fin L,selectionCount l)=
    (∑l:Fin 49962,Module.finrank ℝ (H l.val))+(∑i:Fin 249,(selectedGroup i).count) :=
  by
  rw [selectionCount_raw_split,selectionCount_low_sum,selectionCount_high_sum]

lemma selectionCount_sum : (∑l:Fin L,selectionCount l)=
    (∑l∈Finset.range 49962,Module.finrank ℝ (H l))+
      (selectedGroups.map GroupCertificate.count).sum :=
  by
  rw [selectionCount_split,selectedGroup_count_sum,Fin.sum_univ_eq_sum_range (fun l=>Module.finrank ℝ (H l)) 49962]

end HarmonicCounterexample.Construction

end

noncomputable section


namespace HarmonicCounterexample.Construction
open Certificate
open scoped BigOperators

lemma euclideanDimension_sixteen (k:ℕ) (hk:1≤k) :
    euclideanDimension 16 k=(k+15).choose 15+(k+14).choose 15 := by
  unfold euclideanDimension
  rw [←Nat.choose_symm (by omega : k≤16+k-1),
    ←Nat.choose_symm (by omega : k-1≤16+k-2)]
  congr 1 <;> congr 1 <;> omega

lemma binomRat_add_nat (n a k:ℕ) : binomRat ((n:ℚ)+a) k=((n+a).choose k:ℚ) := by
  rw [←Nat.cast_add,binomRat_nat]

lemma certificate_transport {k m lo s:ℕ}
    (hlo:lo+17=(m+15).choose 15+(m+14).choose 15)
    (hs:binomRat ((k:ℚ)+15) 15+binomRat ((k:ℚ)+14) 15 <
      binomRat ((m:ℚ)+15) 15+binomRat ((m:ℚ)+14) 15-17+(s:ℚ)) :
    (k+15).choose 15+(k+14).choose 15<lo+s := by
  have h15 (a:ℕ) : binomRat ((a:ℚ)+15) 15=((a+15).choose 15:ℚ) :=
    binomRat_add_nat a 15 15
  have h14 (a:ℕ) : binomRat ((a:ℚ)+14) 15=((a+14).choose 15:ℚ) :=
    binomRat_add_nat a 14 15
  rw [h15,h14,h15,h14] at hs
  have hq : (lo:ℚ)+17=((m+15).choose 15:ℚ)+((m+14).choose 15:ℚ) := by
    exact_mod_cast hlo
  have h : ((k+15).choose 15:ℚ)+((k+14).choose 15:ℚ)<(lo:ℚ)+(s:ℚ) := by linarith
  exact_mod_cast h

lemma selectionCount_surplus : euclideanDimension 16 50000 < ∑l:Fin L,selectionCount l := by
  rw [selectionCount_sum,euclideanDimension_sixteen 50000 (by norm_num)]
  apply certificate_transport (m:=49963)
  · rw [show (49963:ℕ)+15=49962+16 by norm_num,
      show (49963:ℕ)+14=49962+15 by norm_num]
    exact low_count_formula 49962
  · exact strict_surplus

end HarmonicCounterexample.Construction

end

end OAI
