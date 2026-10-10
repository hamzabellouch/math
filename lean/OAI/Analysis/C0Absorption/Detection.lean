import OAI.Analysis.C0Absorption.Operations

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
variable {Γ : Type*} {B : CylinderBases Γ}

theorem constant_detector_false (f : C0Ball → ℝ) (hf : BoundedTest (sourceClasses B) c0Origin f)
    (m : ℕ → SourceSpace B) (M : ℝ) (hm : SignedBound m M) {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin f (m i)|) : False := by
  have hh := (hf.weak_null (sourceClasses B) c0Origin m M hm.initial).abs
  have he : ∀ᶠ i in atTop, |completedPairing (sourceClasses B) c0Origin f (m i)| < δ :=
    hh.eventually (show ∀ᶠ x in nhds |(0 : ℝ)|, x<δ by simpa only [abs_zero] using eventually_lt_nhds hδ)
  obtain ⟨i,hi⟩ := he.exists
  exact (not_lt_of_ge (hd i)) hi

theorem tail_remainder_false (f : ℕ → C0Ball → ℝ) (ts : ℕ → List TailOperation)
    (t : ℕ → TailOperation) (ht : ∀ i, t i ∈ ts i) (hg : ∀ i, (t i).isBasic=false)
    (a : ℕ) (ha : ∀ i, (t i).scaleIndex=a) (hN : Tendsto (fun i => (t i).tailIndex) atTop atTop)
    (h : ℕ) (hF : ∀ i, (fun s => f i s*tailProduct (ts i) s) ∈ VClass B h)
    (m : ℕ → SourceSpace B) (M : ℝ) (hm : SignedBound m M) {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin
      (fun s => f i s*tailProduct (ts i) s) (m i)|) : False := by
  apply tail_escape_false (fun i s => f i s*tailProduct (ts i) s) m h hF M hm hδ (dyadic_pos a) hd
    (fun i => (t i).tailIndex+1) (tendsto_atTop_mono (fun i => Nat.le_succ _) hN)
  intro i s hs
  simpa only [ha i,Set.mem_ofPred_eq] using full_tail_support (f i) (ts i) (t i) (ht i) (hg i) hs

theorem fixed_cylinder_tails_false_aux {γ : Γ} (r : GeneratedRepresentation B γ) (h : ℕ)
    (hr : r.operations.length ≤ h) (hj : B.band γ ≤ h) (n : ℕ) :
    ∀ (pre : List TailOperation) (post : ℕ → List TailOperation),
      (∀ i, (post i).length=n) →
      (∀ i, (pre++post i).length ≤ h) →
      (∀ i t, t ∈ pre++post i → t.scaleIndex ≤ h) →
      ∀ (m : ℕ → SourceSpace B) (M : ℝ), SignedBound m M →
      ∀ δ : ℝ, 0 < δ →
      (∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin
        (fun s => r.value s*tailProduct (pre++post i) s) (m i)|) → False := by
  induction n with
  | zero =>
    intro pre post hn hlen hscale m M hm δ hδ hd
    have hz (i : ℕ) : post i=[] := List.length_eq_zero_iff.mp (hn i)
    have hmem : (fun s => r.value s*tailProduct pre s) ∈ VClass B h := by
      refine ⟨γ,r,pre,hr,hj,?_,?_,rfl⟩
      · simpa only [hz 0,List.append_nil] using hlen 0
      · intro t ht
        apply hscale 0 t
        exact List.mem_append.mpr (Or.inl ht)
    apply constant_detector_false _ (VClass_bounded hmem) m M hm hδ
    intro i
    simpa only [hz i,List.append_nil] using hd i
  | succ n ih =>
    intro pre post hn hlen hscale m M hm δ hδ hd
    have hc (i : ℕ) : ∃ t rest, post i=t::rest ∧ rest.length=n := by
      obtain ⟨t,rest,he⟩ := List.length_pos_iff_exists_cons.mp (show 0<(post i).length by rw [hn]; omega)
      refine ⟨t,rest,he,?_⟩
      have hh := hn i
      rw [he,List.length_cons] at hh
      omega
    choose t rest he hrest using hc
    have ht (i : ℕ) : t i ∈ pre++post i := List.mem_append.mpr (Or.inr (by rw [he]; exact List.mem_cons_self))
    rcases TailOperation.constant_or_escape t h (fun i => hscale i _ (ht i)) with
      ⟨p,ψ,hψ,hp⟩ | ⟨ψ,hψ,a,g,ha,hg,hN⟩
    · have heq (i : ℕ) : (pre++[p])++rest (ψ i)=pre++post (ψ i) := by
        rw [he,hp,List.append_assoc,List.singleton_append]
      apply ih (pre++[p]) (fun i => rest (ψ i)) (fun i => hrest _) (fun i => by rw [heq]; exact hlen _)
        (fun i t ht => hscale (ψ i) t (by rw [← heq]; exact ht)) (m ∘ ψ) M
        (hm.subsequence hψ.injective) δ hδ
      intro i
      simpa only [heq,Function.comp_def] using hd (ψ i)
    · let ts0 (i : ℕ) := pre++post (ψ i)
      have hmem0 (i : ℕ) : (fun s => r.value s*tailProduct (ts0 i) s) ∈ VClass B h :=
        ⟨γ,r,ts0 i,hr,hj,hlen _,hscale _,rfl⟩
      cases g with
      | false =>
        exact tail_remainder_false (fun _ => r.value) ts0 (t ∘ ψ) (fun i => ht _) hg a ha hN
          h hmem0 (m ∘ ψ) M (hm.subsequence hψ.injective) hδ (fun i => hd (ψ i))
      | true =>
        let tsA (i : ℕ) := pre++rest (ψ i)
        let tsB (i : ℕ) := pre++(t (ψ i)).remainder::rest (ψ i)
        have hlenA (i : ℕ) : (tsA i).length ≤ h := by
          have hh := hlen (ψ i)
          simp only [he,List.length_append,List.length_cons] at hh
          simp only [tsA,List.length_append]
          omega
        have hscaleA (i : ℕ) (q : TailOperation) (hq : q ∈ tsA i) : q.scaleIndex ≤ h := by
          apply hscale (ψ i) q
          rw [he,List.mem_append,List.mem_cons]
          rcases List.mem_append.mp hq with hq | hq
          · exact Or.inl hq
          · exact Or.inr (Or.inr hq)
        have hlenB (i : ℕ) : (tsB i).length ≤ h := by
          simpa only [tsB,he,List.length_append,List.length_cons] using hlen (ψ i)
        have hscaleB (i : ℕ) (q : TailOperation) (hq : q ∈ tsB i) : q.scaleIndex ≤ h := by
          rcases List.mem_append.mp hq with hq | hq
          · exact hscale (ψ i) q (List.mem_append.mpr (Or.inl hq))
          · rcases List.mem_cons.mp hq with rfl | hq
            · exact hscale (ψ i) (t (ψ i)) (ht _)
            · exact hscaleA i q (List.mem_append.mpr (Or.inr hq))
        let FA (i : ℕ) (s : C0Ball) := r.value s*tailProduct (tsA i) s
        let FB (i : ℕ) (s : C0Ball) := r.value s*tailProduct (tsB i) s
        have hmemA (i : ℕ) : FA i ∈ VClass B h := ⟨γ,r,tsA i,hr,hj,hlenA i,hscaleA i,rfl⟩
        have hmemB (i : ℕ) : FB i ∈ VClass B h := ⟨γ,r,tsB i,hr,hj,hlenB i,hscaleB i,rfl⟩
        have hsplit (i : ℕ) : (fun s => r.value s*tailProduct (ts0 i) s)=fun s => FA i s+FB i s := by
          funext s
          simp only [ts0,he,tailProduct_append,tailProduct_cons,FA,FB,tsA,tsB]
          rw [TailOperation.factor_split _ (hg i)]
          ring
        have hdet (i : ℕ) : δ ≤ |completedPairing (sourceClasses B) c0Origin (FA i) (m (ψ i))+
            completedPairing (sourceClasses B) c0Origin (FB i) (m (ψ i))| := by
          rw [← completedPairing_add _ _ _ _ (VClass_bounded (hmemA i)) (VClass_bounded (hmemB i))]
          rw [← hsplit]
          exact hd (ψ i)
        rcases detection_split _ _ hdet with ⟨η,hη,hdA⟩ | ⟨η,hη,hdB⟩
        · exact ih pre (fun i => rest (ψ (η i))) (fun i => hrest _) (fun i => hlenA _)
            (fun i => hscaleA _) (m ∘ ψ ∘ η) M (hm.subsequence (hψ.comp hη).injective)
            (δ/2) (half_pos hδ) hdA
        · apply tail_remainder_false (fun _ => r.value) (tsB ∘ η) (fun i => (t (ψ (η i))).remainder)
            (fun i => List.mem_append.mpr (Or.inr List.mem_cons_self)) (fun _ => rfl) a
            (fun i => ha _) (hN.comp hη.tendsto_atTop) h (fun i => hmemB _)
            (m ∘ ψ ∘ η) M (hm.subsequence (hψ.comp hη).injective) (half_pos hδ) hdB

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem fixed_cylinder_tails_false {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}
    (r : GeneratedRepresentation B γ) (ts : ℕ → List TailOperation) (h : ℕ)
    (hr : r.operations.length ≤ h) (hj : B.band γ ≤ h)
    (ht : ∀ i, (ts i).length ≤ h) (ha : ∀ i t, t ∈ ts i → t.scaleIndex ≤ h)
    (m : ℕ → SourceSpace B) (M : ℝ) (hm : SignedBound m M)
    {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin
      (fun s => r.value s*tailProduct (ts i) s) (m i)|) : False := by
  obtain ⟨n,φ,hφ,hn⟩ := finite_constant_subsequence
    (fun i => (⟨(ts i).length,Nat.lt_succ_of_le (ht i)⟩ : Fin (h+1)))
  apply fixed_cylinder_tails_false_aux r h hr hj n.val [] (ts ∘ φ)
    (fun i => congrArg Fin.val (hn i)) (fun i => ht _) (fun i => ha _)
    (m ∘ φ) M (hm.subsequence hφ.injective) δ hδ (fun i => hd (φ i))

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

theorem repeated_label_false_aux (h : ℕ) (hj : B.band γ ≤ h) (n : ℕ) :
    ∀ (pre : List (CylinderOperation (B.coordinates γ)))
      (post : ℕ → List (CylinderOperation (B.coordinates γ)))
      (r : ℕ → GeneratedRepresentation B γ) (ts : ℕ → List TailOperation),
    (∀ i, (post i).length=n) → (∀ i, (r i).operations=pre++post i) →
    (∀ i, (r i).operations.length ≤ h) →
    (∀ i, (ts i).length ≤ h) → (∀ i t, t ∈ ts i → t.scaleIndex ≤ h) →
    ∀ (m : ℕ → SourceSpace B) (M : ℝ), SignedBound m M →
    ∀ δ : ℝ, 0<δ →
    (∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin
      (fun s => (r i).value s*tailProduct (ts i) s) (m i)|) → False := by
  induction n with
  | zero =>
    intro pre post r ts hn he hr ht ha m M hm δ hδ hd
    have hz (i : ℕ) : post i=[] := List.length_eq_zero_iff.mp (hn i)
    have hval (i : ℕ) : (r i).value=(r 0).value := by
      simp only [GeneratedRepresentation.value,GeneratedRepresentation.cubeValue,he,hz,List.append_nil]
    apply fixed_cylinder_tails_false (r 0) ts h (hr 0) hj ht ha m M hm hδ
    intro i
    simpa only [hval i] using hd i
  | succ n ih =>
    intro pre post r ts hn he hr ht ha m M hm δ hδ hd
    have hc (i : ℕ) : ∃ t rest, post i=t::rest ∧ rest.length=n := by
      obtain ⟨t,rest,heq⟩ := List.length_pos_iff_exists_cons.mp (show 0<(post i).length by rw [hn]; omega)
      refine ⟨t,rest,heq,?_⟩
      have hh := hn i
      rw [heq,List.length_cons] at hh
      omega
    choose op suf hop hsuf using hc
    have hops (i : ℕ) : (r i).operations=pre++op i::suf i := (he i).trans (congrArg (pre++·) (hop i))
    have hsuflen (i : ℕ) : (suf i).length ≤ h := by
      have hh := hr i
      rw [hops,List.length_append,List.length_cons] at hh
      omega
    have horder (i : ℕ) (t : CylinderOperation (B.coordinates γ)) (ht : t ∈ suf i) : t.scale ≤ (op i).scale := by
      have hh := (r i).ordered
      rw [hops] at hh
      exact (List.pairwise_cons.mp (List.pairwise_append.mp hh).2.1).1 t ht
    rcases CylinderOperation.constant_or_small op with ⟨p,ψ,hψ,hp⟩ | ⟨ψ,hψ,hsmall,g,hg⟩
    · have heq (i : ℕ) : (r (ψ i)).operations=(pre++[p])++suf (ψ i) := by
        rw [hops,hp,List.append_assoc,List.singleton_append]
      exact ih (pre++[p]) (suf ∘ ψ) (r ∘ ψ) (ts ∘ ψ) (fun i => hsuf _) heq
        (fun i => hr _) (fun i => ht _) (fun i => ha _) (m ∘ ψ) M (hm.subsequence hψ.injective) δ hδ (fun i => hd (ψ i))
    · let p : Cube (B.coordinates γ) → ℝ := applyOperations pre (B.base γ)
      have hp : LipschitzWith (4^pre.length*B.L0) p := applyOperations_lipschitz pre (B.base_lipschitz γ)
      cases g with
      | false =>
        apply small_remainders_false (r ∘ ψ) (ts ∘ ψ) h (fun i => hr _) hj (fun i => ht _) (fun i => ha _)
          (op ∘ ψ) hsmall p (4^pre.length*B.L0) hp (suf ∘ ψ) (fun i => hsuflen _) (fun i => horder _) _
          (m ∘ ψ) M (hm.subsequence hψ.injective) hδ (fun i => hd (ψ i))
        intro i
        simp only [Function.comp_def,GeneratedRepresentation.cubeValue,hops,applyOperations_append,applyOperations_cons,p]
        have he' : (op (ψ i)).act p=(op (ψ i)).remainder.act p := by
          simp only [CylinderOperation.act,localOp,hg i,Bool.false_eq_true,↓reduceIte]
          rfl
        exact congrArg (applyOperations (suf (ψ i))) he'
      | true =>
        have hsub (i : ℕ) : (pre++suf (ψ i)).Sublist (r (ψ i)).operations := by
          rw [hops]
          exact (List.sublist_cons_self _ _).append_left pre
        let rA (i : ℕ) := (r (ψ i)).subrepresentation (pre++suf (ψ i)) (hsub i)
        have hsame (i : ℕ) : (pre++(op (ψ i)).remainder::suf (ψ i)).map CylinderOperation.scale =
            (r (ψ i)).operations.map CylinderOperation.scale := by
          simp only [hops,List.map_append,List.map_cons,CylinderOperation.remainder_scale]
        let rB (i : ℕ) := (r (ψ i)).sameScales (pre++(op (ψ i)).remainder::suf (ψ i)) (hsame i)
        have hlenA (i : ℕ) : (rA i).operations.length ≤ h := (hsub i).length_le.trans (hr _)
        have hlenB (i : ℕ) : (rB i).operations.length ≤ h := by
          simpa only [rB,GeneratedRepresentation.sameScales,hops,List.length_append,List.length_cons] using hr (ψ i)
        have hcubeB (i : ℕ) : (rB i).cubeValue=applyOperations (suf (ψ i)) ((op (ψ i)).remainder.act p) := by
          simp only [rB,GeneratedRepresentation.sameScales,GeneratedRepresentation.cubeValue,
            applyOperations_append,applyOperations_cons,p]
        let FA (i : ℕ) (s : C0Ball) := (rA i).value s*tailProduct (ts (ψ i)) s
        let FB (i : ℕ) (s : C0Ball) := (rB i).value s*tailProduct (ts (ψ i)) s
        have hmemA (i : ℕ) : FA i ∈ VClass B h := ⟨γ,rA i,ts (ψ i),hlenA i,hj,ht _,ha _,rfl⟩
        have hmemB (i : ℕ) : FB i ∈ VClass B h := ⟨γ,rB i,ts (ψ i),hlenB i,hj,ht _,ha _,rfl⟩
        have hcube (i : ℕ) : (r (ψ i)).cubeValue=(rA i).cubeValue+(rB i).cubeValue := by
          rw [hcubeB]
          change applyOperations (r (ψ i)).operations (B.base γ)=applyOperations (pre++suf (ψ i)) (B.base γ)+_
          rw [hops,applyOperations_append,applyOperations_cons,applyOperations_append]
          rw [CylinderOperation.act_split _ (hg i),map_add]
        have hsplit (i : ℕ) : (fun s => (r (ψ i)).value s*tailProduct (ts (ψ i)) s)=fun s => FA i s+FB i s := by
          funext s
          simp only [GeneratedRepresentation.value,Function.comp_def,hcube,Pi.add_apply,FA,FB]
          ring
        have hdet (i : ℕ) : δ ≤ |completedPairing (sourceClasses B) c0Origin (FA i) (m (ψ i))+
            completedPairing (sourceClasses B) c0Origin (FB i) (m (ψ i))| := by
          rw [← completedPairing_add _ _ _ _ (VClass_bounded (hmemA i)) (VClass_bounded (hmemB i)),← hsplit]
          exact hd (ψ i)
        rcases detection_split _ _ hdet with ⟨η,hη,hdA⟩ | ⟨η,hη,hdB⟩
        · exact ih pre (suf ∘ ψ ∘ η) (rA ∘ η) (ts ∘ ψ ∘ η) (fun i => hsuf _)
            (fun i => rfl) (fun i => hlenA _) (fun i => ht _) (fun i => ha _)
            (m ∘ ψ ∘ η) M (hm.subsequence (hψ.comp hη).injective) (δ/2) (half_pos hδ) hdA
        · exact small_remainders_false (rB ∘ η) (ts ∘ ψ ∘ η) h (fun i => hlenB _) hj
            (fun i => ht _) (fun i => ha _) (op ∘ ψ ∘ η) (hsmall.comp hη.tendsto_atTop) p
            (4^pre.length*B.L0) hp (suf ∘ ψ ∘ η) (fun i => hsuflen _) (fun i => horder _)
            (fun i => hcubeB _) (m ∘ ψ ∘ η) M (hm.subsequence (hψ.comp hη).injective)
            (half_pos hδ) hdB

theorem repeated_label_false (r : ℕ → GeneratedRepresentation B γ)
    (ts : ℕ → List TailOperation) (h : ℕ)
    (hr : ∀ i, (r i).operations.length ≤ h) (hj : B.band γ ≤ h)
    (ht : ∀ i, (ts i).length ≤ h) (ha : ∀ i t, t ∈ ts i → t.scaleIndex ≤ h)
    (m : ℕ → SourceSpace B) (M : ℝ) (hm : SignedBound m M)
    {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin
      (fun s => (r i).value s*tailProduct (ts i) s) (m i)|) : False := by
  obtain ⟨n,φ,hφ,hn⟩ := finite_constant_subsequence
    (fun i => (⟨(r i).operations.length,Nat.lt_succ_of_le (hr i)⟩ : Fin (h+1)))
  exact repeated_label_false_aux h hj n.val [] (fun i => (r (φ i)).operations) (r ∘ φ) (ts ∘ φ)
    (fun i => congrArg Fin.val (hn i)) (fun i => rfl) (fun i => hr _) (fun i => ht _) (fun i => ha _)
    (m ∘ φ) M (hm.subsequence hφ.injective) δ hδ (fun i => hd (φ i))

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
variable {Γ : Type*} {B : CylinderBases Γ}

namespace GeneratedRepresentation

def relabel {γ γ' : Γ} (r : GeneratedRepresentation B γ) (he : γ=γ') : GeneratedRepresentation B γ' := he ▸ r

@[simp] theorem relabel_length {γ γ' : Γ} (r : GeneratedRepresentation B γ) (he : γ=γ') :
    (r.relabel he).operations.length=r.operations.length := by subst γ'; rfl

@[simp] theorem relabel_value {γ γ' : Γ} (r : GeneratedRepresentation B γ) (he : γ=γ') :
    (r.relabel he).value=r.value := by subst γ'; rfl
end GeneratedRepresentation

theorem bounded_band_detectors_false (loc : RadiusLocalization B)
    (γ : ℕ → Γ) (r : ∀ i, GeneratedRepresentation B (γ i))
    (ts : ℕ → List TailOperation) (h : ℕ)
    (hr : ∀ i, (r i).operations.length ≤ h) (hj : ∀ i, B.band (γ i) ≤ h)
    (ht : ∀ i, (ts i).length ≤ h) (ha : ∀ i t, t ∈ ts i → t.scaleIndex ≤ h)
    (m : ℕ → SourceSpace B) (M : ℝ) (hm : SignedBound m M)
    {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin
      (fun s => (r i).value s*tailProduct (ts i) s) (m i)|) : False := by
  rcases constant_or_injective_subsequence γ with ⟨γ0,ψ,hψ,hγ⟩ | ⟨ψ,hψ,hγ⟩
  · let rr (i : ℕ) := (r (ψ i)).relabel (hγ i)
    apply repeated_label_false rr (ts ∘ ψ) h (fun i => by simpa only [rr,GeneratedRepresentation.relabel_length] using hr (ψ i))
      (by rw [← hγ 0]; exact hj _) (fun i => ht _) (fun i => ha _) (m ∘ ψ) M
      (hm.subsequence hψ.injective) hδ
    intro i
    simpa only [rr,GeneratedRepresentation.relabel_value,Function.comp_def] using hd (ψ i)
  · obtain ⟨j,η,hη,hjη⟩ := finite_constant_subsequence
      (fun i => (⟨B.band (γ (ψ i)),Nat.lt_succ_of_le (hj _)⟩ : Fin (h+1)))
    obtain ⟨H,φ,hφ,F,hF,hdF,hdis⟩ := loc.low_bands_disjoint (γ ∘ ψ ∘ η) (fun i => r (ψ (η i)))
      (ts ∘ ψ ∘ η) h j.val (fun i => hr _) (fun i => congrArg Fin.val (hjη i))
      (Nat.le_of_lt_succ j.isLt) (fun i => ht _) (fun i => ha _) (hγ.comp hη.injective)
      (m ∘ ψ ∘ η) hδ (fun i => hd (ψ (η i)))
    exact VClass_disjoint_false (m ∘ ψ ∘ η ∘ φ) M (hm.subsequence ((hψ.comp hη).comp hφ).injective)
      F H hF hdis (half_pos hδ) hdF

theorem source_detectors_false (locT : TagLocalization B) (locR : RadiusLocalization B)
    (m : ℕ → SourceSpace B) (M : ℝ) (hm : SignedBound m M)
    (F : ℕ → C0Ball → ℝ) (d : ℕ) (hF : ∀ i, F i ∈ sourceClasses B d)
    {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin (F i) (m i)|) : False := by
  let h := d/2+1
  by_cases hdEven : d%2=0
  · have ht (i : ℕ) : F i ∈ TClass B h := by simpa only [sourceClasses,hdEven,↓reduceIte,h] using hF i
    choose γ r hr he using ht
    have hdet (i : ℕ) : δ ≤ |completedPairing (sourceClasses B) c0Origin (r i).value (m i)| := by
      simpa only [he i] using hd i
    rcases nat_constant_or_tendsto (fun i => B.band (γ i)) with ⟨j,ψ,hψ,hj⟩ | hj
    · apply bounded_band_detectors_false locR (γ ∘ ψ) (fun i => r (ψ i)) (fun _ => []) (h+j)
        (fun i => (hr _).trans (Nat.le_add_right h j)) (fun i => by change B.band (γ (ψ i)) ≤ h+j; rw [hj]; omega)
        (by simp) (by simp) (m ∘ ψ) M (hm.subsequence hψ.injective) hδ
      intro i
      simpa only [tailProduct_nil,mul_one,Function.comp_def] using hdet (ψ i)
    · obtain ⟨φ,hφ,G,hG,hdG,hLip⟩ := high_bands_compatible locT γ r h hr hj m hδ hdet
      apply compatible_detectors_false (sourceClasses B) c0Origin (m ∘ φ) M (hm.subsequence hφ.injective)
        G (2*h) (4^(h+1)*B.L0+1) _ hLip (half_pos hδ) hdG
      intro i
      simpa only [sourceClasses_even] using hG i
  · have ht (i : ℕ) : F i ∈ VClass B h := by simpa only [sourceClasses,hdEven,↓reduceIte,h] using hF i
    choose γ r ts hr hj hts ha he using ht
    apply bounded_band_detectors_false locR γ r ts h hr hj hts ha m M hm hδ
    intro i
    simpa only [he i] using hd i

theorem source_no_bounded_signs_lower (locT : TagLocalization B) (locR : RadiusLocalization B)
    (m : ℕ → SourceSpace B) (M r : ℝ) (hm : SignedBound m M) (hr : 0 < r)
    (hlower : ∀ i, r ≤ ‖m i‖) : False := by
  obtain ⟨h,δ,hδ,φ,hφ,F,hF⟩ := one_class_detects (sourceClasses B) c0Origin m M r hr hlower hm.initial
  exact source_detectors_false locT locR (m ∘ φ) M (hm.subsequence hφ.injective) F h
    (fun i => (hF i).1) hδ (fun i => (hF i).2)

theorem atoms_signed_bound : SignedBound atom 1 := by
  classical
  intro n ι hι ε
  apply c0_norm_le _ zero_le_one
  intro k
  change |c0Eval k (∑ i, realSign (ε i) • atom (ι i))| ≤ 1
  simp only [map_sum,map_smul,smul_eq_mul,c0Eval_apply,atom_apply]
  by_cases hex : ∃ i, ι i=k
  · obtain ⟨i,hi⟩ := hex
    rw [Finset.sum_eq_single i]
    · simpa only [hi,ite_true,mul_one] using (abs_realSign (ε i)).le
    · intro j hj hji
      have hneq : ι j≠k := by intro he; exact hji (hι (he.trans hi.symm))
      simp only [hneq,ite_false,mul_zero]
    · simp
  · push Not at hex
    simp only [hex,ite_false,mul_zero,Finset.sum_const_zero,abs_zero,zero_le_one]

theorem source_noLinearC0 (locT : TagLocalization B) (locR : RadiusLocalization B) :
    NoLinearC0 (SourceSpace B) := by
  intro T hT
  obtain ⟨c,hc,hcT⟩ := hT
  let m (i : ℕ) := T (atom i)
  have hm : SignedBound m ‖T‖ := by
    intro n ι hι ε
    change ‖∑ i, realSign (ε i) • T (atom (ι i))‖ ≤ ‖T‖
    rw [show (∑ i, realSign (ε i) • T (atom (ι i))) = T (∑ i, realSign (ε i) • atom (ι i)) by simp only [map_sum,map_smul]]
    calc
      _ ≤ ‖T‖ * ‖∑ i, realSign (ε i) • atom (ι i)‖ := T.le_opNorm _
      _ ≤ ‖T‖*1 := mul_le_mul_of_nonneg_left (atoms_signed_bound n ι hι ε) (ContinuousLinearMap.opNorm_nonneg T)
      _ = ‖T‖ := mul_one _
  exact source_no_bounded_signs_lower locT locR m ‖T‖ c hm hc
    (fun i => by simpa only [atom_norm,mul_one] using hcT (atom i))

end
end C0Absorption

end OAI
