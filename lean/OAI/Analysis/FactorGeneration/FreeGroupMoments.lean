import OAI.Analysis.FactorGeneration.HaarSequences

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Every nonempty reduced word in successive Haar variables has zero trace.
The induction eliminates the largest label, retaining centered lower-label gaps. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def unitaryWord {A : Type*} (v : A → unitary (Q τ ω)) (w : List (A × Bool)) : Q τ ω :=
  (w.map (fun x => algebraSignedLetter (v x.1 : Q τ ω) (!x.2))).prod

theorem unitaryWord_nil {A : Type*} (v : A → unitary (Q τ ω)) :
    unitaryWord τ ω v []=1 := rfl

theorem unitaryWord_cons {A : Type*} (v : A → unitary (Q τ ω))
    (x : A × Bool) (w : List (A × Bool)) :
    unitaryWord τ ω v (x::w)=algebraSignedLetter (v x.1 : Q τ ω) (!x.2)*unitaryWord τ ω v w := rfl

theorem unitaryWord_append {A : Type*} (v : A → unitary (Q τ ω))
    (a b : List (A × Bool)) : unitaryWord τ ω v (a++b)=unitaryWord τ ω v a*unitaryWord τ ω v b := by
  simp [unitaryWord,List.map_append,List.prod_append]

theorem unitaryWord_mem {A : Type*} (v : A → unitary (Q τ ω))
    (D : StarSubalgebra ℂ (Q τ ω)) (w : List (A × Bool))
    (hv : ∀ x ∈ w,(v x.1 : Q τ ω) ∈ D) : unitaryWord τ ω v w ∈ D := by
  induction w with
  | nil => exact D.one_mem
  | cons x w ih =>
    apply D.mul_mem _ (ih (fun y hy => hv y (by simp [hy])))
    have hx := hv x (by simp)
    change algebraSignedLetter (v x.1 : Q τ ω) (!x.2) ∈ D
    unfold algebraSignedLetter
    split
    · exact star_mem hx
    · exact hx

/-- Scan the tail after a maximal label. Empty gaps can only join equal signs. -/
theorem maximal_word_gaps (v : ℕ → unitary (Q τ ω))
    (D : StarSubalgebra ℂ (Q τ ω)) (n : ℕ)
    (hv : ∀ i < n,(v i : Q τ ω) ∈ D)
    (hzero : ∀ a : List (ℕ × Bool),FreeGroup.IsReduced a → a ≠ [] →
      (∀ x ∈ a,x.1 < n) → quotientTrace τ ω (unitaryWord τ ω v a)=0)
    (w : List (ℕ × Bool)) (s : Bool)
    (hr : FreeGroup.IsReduced ((n,s)::w)) (hn : ∀ x ∈ w,x.1 ≤ n) :
    ∃ xs b,b ∈ D ∧ SignedReducedGaps τ ω D.toSubalgebra (!s) xs ∧
      unitaryWord τ ω v ((n,s)::w)=betweenWord (v n : Q τ ω) (!s) xs b := by
  classical
  by_cases hex : ∃ x ∈ w,x.1=n
  · obtain ⟨a,t,c,he,ha⟩ := word_split_first n w hex
    have hlt : ∀ x ∈ a,x.1 < n := by
      intro x hx
      have := hn x (by rw [he]; simp [hx])
      have := ha x hx
      omega
    have har : FreeGroup.IsReduced a := reduced_append_left (he ▸ reduced_tail hr)
    have hcr : FreeGroup.IsReduced ((n,t)::c) := reduced_append_right (he ▸ reduced_tail hr)
    have hcn : ∀ x ∈ c,x.1 ≤ n := by
      intro x hx
      exact hn x (by rw [he]; simp [hx])
    obtain ⟨xs,b,hb,hxs,hev⟩ := maximal_word_gaps v D n hv hzero c t hcr hcn
    have ham : unitaryWord τ ω v a ∈ D := unitaryWord_mem τ ω v D a (fun x hx => hv _ (hlt x hx))
    have hac : (!s) ≠ (!t) → quotientTrace τ ω (unitaryWord τ ω v a)=0 := by
      intro hst
      apply hzero a har _ hlt
      intro hempty
      have hr' : FreeGroup.IsReduced ((n,s)::(n,t)::c) := by
        simpa only [he,hempty,List.nil_append] using hr
      have hst' : s=t := (FreeGroup.isReduced_cons_cons.mp hr').1 rfl
      exact hst (congrArg Bool.not hst')
    refine ⟨(unitaryWord τ ω v a,!t)::xs,b,hb,⟨ham,hac,hxs⟩,?_⟩
    rw [unitaryWord_cons,he,unitaryWord_append,hev]
    simp only [betweenWord,mul_assoc]
  · refine ⟨[],unitaryWord τ ω v w,?_,trivial,rfl⟩
    apply unitaryWord_mem τ ω v D w
    intro x hx
    apply hv
    have := hn x hx
    have : x.1 ≠ n := fun he => hex ⟨x,hx,he⟩
    omega
termination_by w.length
 decreasing_by simp only [he,List.length_append,List.length_cons]; omega

theorem successive_reduced_word_zero (v : ℕ → unitary (Q τ ω))
    (D : ℕ → StarSubalgebra ℂ (Q τ ω))
    (hv : ∀ i j,i < j → (v i : Q τ ω) ∈ D j)
    (hep : ∀ j,HaarEndpoints τ ω (D j).toSubalgebra (v j))
    (n : ℕ) (w : List (ℕ × Bool)) (hr : FreeGroup.IsReduced w) (hw : w ≠ [])
    (hn : ∀ x ∈ w,x.1 < n) : quotientTrace τ ω (unitaryWord τ ω v w)=0 := by
  classical
  induction n generalizing w with
  | zero =>
    cases w with
    | nil => exact (hw rfl).elim
    | cons x w => have := hn x (by simp); omega
  | succ n ih =>
    by_cases hex : ∃ x ∈ w,x.1=n
    · obtain ⟨a,s,b,he,ha⟩ := word_split_first n w hex
      have halt : ∀ x ∈ a,x.1 < n := by
        intro x hx
        have := hn x (by rw [he]; simp [hx])
        have := ha x hx
        omega
      have hbr : FreeGroup.IsReduced ((n,s)::b) := reduced_append_right (he ▸ hr)
      have hbn : ∀ x ∈ b,x.1 ≤ n := by
        intro x hx
        have := hn x (by rw [he]; simp [hx])
        omega
      obtain ⟨xs,c,hc,hxs,hev⟩ := maximal_word_gaps τ ω v (D n) n
        (fun i hi => hv i n hi) ih b s hbr hbn
      rw [he,unitaryWord_append,hev]
      exact (hep n).signed_gaps τ ω _
        (unitaryWord_mem τ ω v (D n) a (fun x hx => hv _ _ (halt x hx))) c hc _ xs hxs
    · apply ih w hr hw
      intro x hx
      have := hn x hx
      have : x.1 ≠ n := fun he => hex ⟨x,hx,he⟩
      omega

end

/-! The actual free-group representation furnished by successive Haar variables. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def unitaryRepresentation {A : Type*} (v : A → unitary (Q τ ω)) :
    FreeGroup A →* unitary (Q τ ω) := FreeGroup.lift v

theorem unitaryRepresentation_mk {A : Type*} (v : A → unitary (Q τ ω))
    (w : List (A × Bool)) :
    (unitaryRepresentation τ ω v (FreeGroup.mk w) : Q τ ω)=unitaryWord τ ω v w := by
  rw [unitaryRepresentation,FreeGroup.lift_mk]
  induction w with
  | nil => rfl
  | cons x w ih =>
    simp only [List.map_cons,List.prod_cons,Submonoid.coe_mul,unitaryWord_cons,ih]
    cases x.2 <;> rfl

theorem successive_freeGroup_trace (v : ℕ → unitary (Q τ ω))
    (D : ℕ → StarSubalgebra ℂ (Q τ ω))
    (hv : ∀ i j,i < j → (v i : Q τ ω) ∈ D j)
    (hep : ∀ j,HaarEndpoints τ ω (D j).toSubalgebra (v j))
    (g : FreeGroup ℕ) (hg : g ≠ 1) :
    quotientTrace τ ω (unitaryRepresentation τ ω v g : Q τ ω)=0 := by
  rw [← FreeGroup.mk_toWord (x := g),unitaryRepresentation_mk]
  apply successive_reduced_word_zero τ ω v D hv hep
    (g.toWord.toFinset.sup Prod.fst+1) g.toWord FreeGroup.isReduced_toWord
    (fun h => hg (FreeGroup.toWord_eq_nil_iff.mp h))
  intro x hx
  have := Finset.le_sup (f := Prod.fst) (List.mem_toFinset.mpr hx)
  omega

/-- Zero nonidentity moments imply faithfulness, since the unit has trace one. -/
theorem unitaryRepresentation_injective {A : Type*} (v : A → unitary (Q τ ω))
    (hzero : ∀ g : FreeGroup A,g ≠ 1 →
      quotientTrace τ ω (unitaryRepresentation τ ω v g : Q τ ω)=0) :
    Function.Injective (unitaryRepresentation τ ω v) := by
  apply (injective_iff_map_eq_one (unitaryRepresentation τ ω v)).mpr
  intro g hg
  by_contra hne
  have ht := hzero g hne
  rw [hg] at ht
  have : (1 : ℂ)=0 := (quotientTrace_one τ ω).symm.trans ht
  exact one_ne_zero this

theorem unitaryRepresentation_gram {A : Type*} [DecidableEq A]
    (v : A → unitary (Q τ ω))
    (hzero : ∀ g : FreeGroup A,g ≠ 1 →
      quotientTrace τ ω (unitaryRepresentation τ ω v g : Q τ ω)=0)
    (g h : FreeGroup A) :
    quotientTrace τ ω (star (unitaryRepresentation τ ω v g : Q τ ω)*
      (unitaryRepresentation τ ω v h : Q τ ω))=if g=h then 1 else 0 := by
  have he : star (unitaryRepresentation τ ω v g : Q τ ω)*
      (unitaryRepresentation τ ω v h : Q τ ω)=
      (unitaryRepresentation τ ω v (g⁻¹*h) : Q τ ω) := by
    exact (congrArg (fun a : unitary (Q τ ω) => (a : Q τ ω))
      (((unitaryRepresentation τ ω v).map_mul (g⁻¹) h).trans
        (congrArg (fun a => a*unitaryRepresentation τ ω v h)
          ((unitaryRepresentation τ ω v).map_inv g)))).symm
  apply (congrArg (quotientTrace τ ω) he).trans
  by_cases hgh : g=h
  · subst h
    rw [_root_.inv_mul_cancel,map_one,ite_eq_left rfl]
    exact quotientTrace_one τ ω
  · rw [ite_eq_right hgh]
    exact hzero _ (fun heq => hgh (_root_.inv_mul_eq_one.mp heq))

variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

theorem SuccessiveCoordinateHaar.freeGroup_trace
    (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u : unitary (Q τ ω)) (hu : (u : Q τ ω) ∈ seed)
    (g : FreeGroup ℕ) (hg : g ≠ 1) :
    quotientTrace τ ω
      (unitaryRepresentation τ ω (prefixVariable τ ω u (fun k => (F.step k).t)) g : Q τ ω)=0 :=
  successive_freeGroup_trace τ ω _ F.algebra
    (fun _ _ hij => F.variable_mem τ ω u hu hij) (F.variable_endpoints τ ω u hu) g hg

theorem SuccessiveCoordinateHaar.freeGroup_injective
    (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u : unitary (Q τ ω)) (hu : (u : Q τ ω) ∈ seed) :
    Function.Injective (unitaryRepresentation τ ω (prefixVariable τ ω u (fun k => (F.step k).t))) :=
  unitaryRepresentation_injective τ ω _ (F.freeGroup_trace τ ω u hu)

theorem SuccessiveCoordinateHaar.freeGroup_gram
    (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u : unitary (Q τ ω)) (hu : (u : Q τ ω) ∈ seed) (g h : FreeGroup ℕ) :
    quotientTrace τ ω
      (star (unitaryRepresentation τ ω (prefixVariable τ ω u (fun k => (F.step k).t)) g : Q τ ω)*
        (unitaryRepresentation τ ω (prefixVariable τ ω u (fun k => (F.step k).t)) h : Q τ ω))=
      if g=h then 1 else 0 :=
  unitaryRepresentation_gram τ ω _ (F.freeGroup_trace τ ω u hu) g h

end

/-! Reduced-word moments for p*y*(star p). Distinct labels have centered ratios;
reducedness requires distinct labels precisely at opposite-sign gaps. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {A : Type*}

def conjugateVariables (p : A → unitary (Q τ ω)) (y : unitary (Q τ ω))
    (a : A) : unitary (Q τ ω) := p a*y*star (p a)

def conjugateGaps (p : A → unitary (Q τ ω)) (a : A × Bool) :
    List (A × Bool) → List (Q τ ω × Bool)
  | [] => []
  | b::w => ((↑(star (p a.1)*p b.1) : Q τ ω),!b.2)::conjugateGaps p b w

def conjugateEnd (p : A → unitary (Q τ ω)) (a : A × Bool) : List (A × Bool) → Q τ ω
  | [] => ↑(star (p a.1))
  | b::w => conjugateEnd p b w

theorem signed_conjugate (p y : unitary (Q τ ω)) (s : Bool) :
    algebraSignedLetter (↑(p*y*(star p)) : Q τ ω) s=
      (p : Q τ ω)*algebraSignedLetter (y : Q τ ω) s*↑(star p) := by
  cases s with
  | false => rfl
  | true =>
    change star ((p : Q τ ω)*(y : Q τ ω)*star (p : Q τ ω))=
      (p : Q τ ω)*star (y : Q τ ω)*star (p : Q τ ω)
    rw [star_mul,star_mul,star_star,mul_assoc]

theorem conjugateWord_formula (p : A → unitary (Q τ ω)) (y : unitary (Q τ ω))
    (a : A × Bool) (w : List (A × Bool)) :
    unitaryWord τ ω (conjugateVariables τ ω p y) (a::w)=
      (p a.1 : Q τ ω)*betweenWord (y : Q τ ω) (!a.2)
        (conjugateGaps τ ω p a w) (conjugateEnd τ ω p a w) := by
  induction w generalizing a with
  | nil =>
    rw [unitaryWord_cons,unitaryWord_nil,mul_one]
    change algebraSignedLetter (↑(p a.1*y*star (p a.1)) : Q τ ω) (!a.2)=_
    rw [signed_conjugate]
    exact mul_assoc _ _ _
  | cons b w ih =>
    rw [unitaryWord_cons,ih]
    change algebraSignedLetter (↑(p a.1*y*star (p a.1)) : Q τ ω) (!a.2)*_= _
    rw [signed_conjugate]
    simp only [conjugateGaps,conjugateEnd,betweenWord,Submonoid.coe_mul,mul_assoc]

theorem conjugateEnd_mem (p : A → unitary (Q τ ω))
    (D : StarSubalgebra ℂ (Q τ ω)) (hp : ∀ a,(p a : Q τ ω) ∈ D)
    (a : A × Bool) (w : List (A × Bool)) : conjugateEnd τ ω p a w ∈ D := by
  induction w generalizing a with
  | nil => exact star_mem (hp a.1)
  | cons b w ih => exact ih b

theorem conjugateGaps_reduced (p : A → unitary (Q τ ω))
    (D : StarSubalgebra ℂ (Q τ ω)) (hp : ∀ a,(p a : Q τ ω) ∈ D)
    (hzero : ∀ a b,a ≠ b → quotientTrace τ ω (↑(star (p a)*p b) : Q τ ω)=0)
    (a : A × Bool) (w : List (A × Bool)) (hr : FreeGroup.IsReduced (a::w)) :
    SignedReducedGaps τ ω D.toSubalgebra (!a.2) (conjugateGaps τ ω p a w) := by
  induction w generalizing a with
  | nil => trivial
  | cons b w ih =>
    have ha : star (p a.1 : Q τ ω) ∈ D := star_mem (hp a.1)
    refine ⟨D.mul_mem ha (hp b.1),?_,ih b (reduced_tail hr)⟩
    intro hsign
    apply hzero
    intro he
    exact hsign (congrArg Bool.not ((FreeGroup.isReduced_cons_cons.mp hr).1 he))

theorem conjugate_reduced_word_zero (p : A → unitary (Q τ ω))
    (D : StarSubalgebra ℂ (Q τ ω)) (hp : ∀ a,(p a : Q τ ω) ∈ D)
    (hzero : ∀ a b,a ≠ b → quotientTrace τ ω (↑(star (p a)*p b) : Q τ ω)=0)
    (y : unitary (Q τ ω)) (hy : HaarEndpoints τ ω D.toSubalgebra y)
    (w : List (A × Bool)) (hr : FreeGroup.IsReduced w) (hw : w ≠ []) :
    quotientTrace τ ω (unitaryWord τ ω (conjugateVariables τ ω p y) w)=0 := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons a w =>
    rw [conjugateWord_formula]
    exact hy.signed_gaps τ ω _ (hp a.1) _ (conjugateEnd_mem τ ω p D hp a w)
      _ _ (conjugateGaps_reduced τ ω p D hp hzero a w hr)

theorem conjugate_freeGroup_trace [DecidableEq A] (p : A → unitary (Q τ ω))
    (D : StarSubalgebra ℂ (Q τ ω)) (hp : ∀ a,(p a : Q τ ω) ∈ D)
    (hzero : ∀ a b,a ≠ b → quotientTrace τ ω (↑(star (p a)*p b) : Q τ ω)=0)
    (y : unitary (Q τ ω)) (hy : HaarEndpoints τ ω D.toSubalgebra y)
    (g : FreeGroup A) (hg : g ≠ 1) :
    quotientTrace τ ω (unitaryRepresentation τ ω (conjugateVariables τ ω p y) g : Q τ ω)=0 := by
  rw [← FreeGroup.mk_toWord (x := g),unitaryRepresentation_mk]
  exact conjugate_reduced_word_zero τ ω p D hp hzero y hy g.toWord
    FreeGroup.isReduced_toWord (fun h => hg (FreeGroup.toWord_eq_nil_iff.mp h))

end

/-! Positive and negative conjugate terms in first-order correlation. Same-sign gaps require no centering hypothesis. -/
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {D : StarSubalgebra ℂ (Q τ ω)} {W : unitary (Q τ ω)}

theorem HaarEndpoints.base_correlation (hW : HaarEndpoints τ ω D.toSubalgebra W)
    (xi : Q τ ω) (hxi : xi ∈ D) : quotientTrace τ ω (star xi*(W : Q τ ω))=0 := by
  have hstar : star xi ∈ D := star_mem hxi
  have h := hW.signed_gaps τ ω (star xi) hstar 1 D.one_mem false [] trivial
  simpa only [betweenWord,algebraSignedLetter,Bool.false_eq_true,ite_false,mul_one] using h

theorem HaarEndpoints.positive_conjugate_correlation
    (hW : HaarEndpoints τ ω D.toSubalgebra W)
    (xi : Q τ ω) (hxi : xi ∈ D) (p z : unitary (Q τ ω))
    (hp : (p : Q τ ω) ∈ D) (hz : (z : Q τ ω) ∈ D)
    (hcenter : quotientTrace τ ω (star (p : Q τ ω))=0) :
    quotientTrace τ ω (star xi*(↑(p*(z*star W)*star p) : Q τ ω)*(W : Q τ ω))=0 := by
  have hstar : star xi ∈ D := star_mem hxi
  have hpstar : star (p : Q τ ω) ∈ D := star_mem hp
  have h := hW.signed_gaps τ ω (star xi*(p : Q τ ω)*(z : Q τ ω))
    (D.mul_mem (D.mul_mem hstar hp) hz) 1 D.one_mem true [(star (p : Q τ ω),false)]
    ⟨hpstar,fun _ => hcenter,trivial⟩
  change quotientTrace τ ω ((star xi*(p : Q τ ω)*(z : Q τ ω))*
    (star (W : Q τ ω)*star (p : Q τ ω)*((W : Q τ ω)*1)))=0 at h
  simpa only [Submonoid.coe_mul,Unitary.coe_star,mul_one,mul_assoc] using h

theorem HaarEndpoints.negative_conjugate_correlation
    (hW : HaarEndpoints τ ω D.toSubalgebra W)
    (xi : Q τ ω) (hxi : xi ∈ D) (p z : unitary (Q τ ω))
    (hp : (p : Q τ ω) ∈ D) (hz : (z : Q τ ω) ∈ D) :
    quotientTrace τ ω (star xi*star (↑(p*(z*star W)*star p) : Q τ ω)*(W : Q τ ω))=0 := by
  have hstar : star xi ∈ D := star_mem hxi
  have hpstar : star (p : Q τ ω) ∈ D := star_mem hp
  have hzstar : star (z : Q τ ω) ∈ D := star_mem hz
  have h := hW.signed_gaps τ ω (star xi*(p : Q τ ω)) (D.mul_mem hstar hp)
    1 D.one_mem false [(star (z : Q τ ω)*star (p : Q τ ω),false)]
    ⟨D.mul_mem hzstar hpstar,fun hh => (hh rfl).elim,trivial⟩
  change quotientTrace τ ω ((star xi*(p : Q τ ω))*
    ((W : Q τ ω)*(star (z : Q τ ω)*star (p : Q τ ω))*((W : Q τ ω)*1)))=0 at h
  simpa only [Submonoid.coe_mul,Unitary.coe_star,star_mul,star_star,mul_one,mul_assoc] using h

end Generator.Tracial

end

end OAI
