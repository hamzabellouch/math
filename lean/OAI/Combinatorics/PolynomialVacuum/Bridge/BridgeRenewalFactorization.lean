import OAI.Combinatorics.PolynomialVacuum.Bridge.BridgeWord

namespace OAI

namespace PolynomialVacuumBridge.Corridor.BridgeWord

 

theorem residue (A B C D : BridgeWord) (r : List Bool)
    (hC : C.word=A.word++r) (hB : B.word=r++D.word) :
    ∃ E : BridgeWord, E.word=r ∧ C=A*E ∧ B=E*D := by
  by_cases hr : r=[]
  · subst r
    have hCA : C=A := ext (by simpa using hC)
    have hBD : B=D := ext (by simpa using hB)
    exact ⟨1,rfl,by simpa using hCA,by simpa using hBD⟩
  have ht : traced bottomSource C.word=traced bottomSource A.word++
      (traced bottomSource r).map (shiftVertex A.endX A.height) := by
    rw [hC,traced_append,A.terminal_source,← shift_traced]
  have hCt : terminalGerm (shiftGerm A.endX A.height bottomSource) r=(.up C.endX C.height,0) := by
    simpa only [hC,terminalGerm_append,A.terminal_source] using C.terminal
  have hlo : ∀ v∈traced bottomSource r, 0≤layer v := by
    intro v hv
    exact (B.inStrip v (by rw [hB,traced_append]; simp [hv])).1
  have hhi : ∀ v∈traced bottomSource r, layer v+(A.height : ℤ)<(C.height : ℤ) := by
    intro v hv
    have := (C.inStrip (shiftVertex A.endX A.height v) (by
      rw [ht]
      exact List.mem_append_right _ (List.mem_map.mpr ⟨v,hv,rfl⟩))).2
    simpa only [layer_shift] using this
  have hAC : A.height<C.height := by
    obtain ⟨b,w,he⟩ := List.exists_cons_of_ne_nil hr
    have := hhi bottomSource.1 (by simp [he,traced])
    norm_num [bottomSource,layer] at this
    exact this
  let E : BridgeWord := {
    word := r
    height := C.height-A.height
    endX := C.endX-A.endX
    distinct := by
      have hn := (List.nodup_append.mp (ht ▸ C.distinct)).2.1
      exact hn.of_map _
    terminal := by
      have hh := congrArg (shiftGerm (-A.endX) (-(A.height : ℤ))) hCt
      simp only [← shift_terminal,shiftGerm_add,neg_add_cancel,shiftGerm_zero] at hh
      simpa [shiftGerm,shiftVertex,sub_eq_add_neg,Nat.cast_sub hAC.le] using hh
    inStrip := by
      intro v hv
      refine ⟨hlo v hv,?_⟩
      rw [Nat.cast_sub hAC.le]
      have := hhi v hv
      omega }
  have hCE : C=A*E := by apply ext; exact hC
  have hBE : B=E*D := by apply ext; exact hB
  exact ⟨E,rfl,hCE,hBE⟩

instance : IsLeftCancelMul BridgeWord where
  mul_left_cancel _ _ _ h := ext (List.append_cancel_left (congrArg BridgeWord.word h))
instance : IsRightCancelMul BridgeWord where
  mul_right_cancel _ _ _ h := ext (List.append_cancel_right (congrArg BridgeWord.word h))

theorem primitive_first_unique (A B C D : BridgeWord)
    (hA : A.IsPrimitive) (hC : C.IsPrimitive) (he : A*B=C*D) : A=C ∧ B=D := by
  have hw := congrArg BridgeWord.word he
  change A.word++B.word=C.word++D.word at hw
  rcases List.append_eq_append_iff.mp hw with ⟨r,hCw,hBw⟩ | ⟨r,hAw,hDw⟩
  · obtain ⟨E,_,hCE,hBE⟩ := residue A B C D r hCw hBw
    rcases hC.2 A E hCE with hf | hf
    · exact False.elim (hA.1 hf)
    · subst E
      simp only [mul_one,one_mul] at hCE hBE
      exact ⟨hCE.symm,hBE⟩
  · obtain ⟨E,_,hAE,hDE⟩ := residue C D A B r hAw hDw
    rcases hA.2 C E hAE with hf | hf
    · exact False.elim (hC.1 hf)
    · subst E
      simp only [mul_one,one_mul] at hAE hDE
      exact ⟨hAE,hDE.symm⟩

theorem exists_primitive_factors (A : BridgeWord) :
    ∃ L : List BridgeWord, (∀ B∈L, B.IsPrimitive) ∧ L.prod=A := by
  classical
  induction h : A.word.length using Nat.strong_induction_on generalizing A with
  | h n ih =>
    by_cases he : A=1
    · exact ⟨[],by simp,by simp [he]⟩
    by_cases hp : A.IsPrimitive
    · exact ⟨[A],by simpa,by simp⟩
    obtain ⟨B,C,hA,hB,hC⟩ : ∃ B C, A=B*C ∧ B≠1 ∧ C≠1 := by
      simpa [IsPrimitive,he,not_or] using hp
    have hlen : n=B.word.length+C.word.length := by simpa [hA] using h.symm
    have hBp : 0<B.word.length := List.length_pos_iff.mpr (fun hb => hB (word_eq_nil.mp hb))
    have hCp : 0<C.word.length := List.length_pos_iff.mpr (fun hc => hC (word_eq_nil.mp hc))
    obtain ⟨LB,hLB,eLB⟩ := ih B.word.length (by omega) B rfl
    obtain ⟨LC,hLC,eLC⟩ := ih C.word.length (by omega) C rfl
    exact ⟨LB++LC,by simp only [List.mem_append]; intro p hp; exact hp.elim (hLB p) (hLC p),
      by simp [eLB,eLC,hA]⟩

theorem primitive_prod_ne_one (L : List BridgeWord) (hL : ∀ A∈L, A.IsPrimitive)
    (hne : L≠[]) : L.prod≠1 := by
  obtain ⟨A,L,rfl⟩ := List.exists_cons_of_ne_nil hne
  intro he
  have hs := congrArg (fun B : BridgeWord => B.word.length) he
  have ha := (hL A (by simp)).1
  simp only [List.prod_cons,word_mul,List.length_append,word_one,List.length_nil] at hs
  exact ha (word_eq_nil.mp (List.eq_nil_of_length_eq_zero (by omega)))

theorem primitive_factorization_unique (L K : List BridgeWord)
    (hL : ∀ A∈L, A.IsPrimitive) (hK : ∀ A∈K, A.IsPrimitive) (he : L.prod=K.prod) : L=K := by
  induction L generalizing K with
  | nil =>
    have hk : K=[] := by
      by_contra hn
      exact primitive_prod_ne_one K hK hn he.symm
    simp [hk]
  | cons A L ih =>
    cases K with
    | nil => exact False.elim (primitive_prod_ne_one _ hL (by simp) he)
    | cons C K =>
      obtain ⟨hac,hlk⟩ := primitive_first_unique A L.prod C K.prod
        (hL A (by simp)) (hK C (by simp)) he
      subst C
      exact congrArg (List.cons A) (ih K (fun p hp => hL p (by simp [hp]))
        (fun p hp => hK p (by simp [hp])) hlk)

end PolynomialVacuumBridge.Corridor.BridgeWord

end OAI
