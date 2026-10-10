import OAI.Combinatorics.ThinTrees.SpectralPacking

namespace OAI

universe uV uI uV2 uV3 uI2 uJ

section
open scoped Classical
open Matrix

namespace StrongThinTree.Geometry
noncomputable section
open Finset
open scoped Classical
variable {V : Type uV} {I : Type uI} [DecidableEq V] [DecidableEq I] {h : ℕ}

omit [DecidableEq V] in
lemma distance_balls_disjoint (X : V → Fin h → ℝ) (u v : V) {r : ℝ}
    (hsep : 2*r ≤ l1dist (X u) (X v)) :
    Disjoint ((RadialShell.ball u r).support X) ((RadialShell.ball v r).support X) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  have hx := l1dist_triangle (X u) z (X v)
  rw [l1dist_comm (X u) z] at hx
  have hz₁ := hz.2.1
  have hz₂ := hz'.2.1
  change l1dist z (X u) < r at hz₁
  change l1dist z (X v) < r at hz₂
  linarith

lemma l1_separated_net (X : V → Fin h → ℝ) (F : Finset V) (hF : F.Nonempty)
    {r : ℝ} (hr : 0 ≤ r) :
    ∃S : Finset V, S ⊆ F ∧ S.Nonempty ∧
      (∀u ∈ S, ∀v ∈ S, u ≠ v → r < l1dist (X u) (X v)) ∧
      ∀u ∈ F, ∃v ∈ S, l1dist (X u) (X v) ≤ r := by
  let sep : Finset V → Prop := fun S => ∀u ∈ S, ∀v ∈ S, u ≠ v → r < l1dist (X u) (X v)
  let good := F.powerset.filter sep
  have hgood : good.Nonempty := ⟨∅,mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _),by simp [sep]⟩⟩
  obtain ⟨S,hS,hmax⟩ := exists_max_image good card hgood
  obtain ⟨hSF,hsep⟩ := mem_filter.mp hS
  have hcover : ∀u ∈ F, ∃v ∈ S, l1dist (X u) (X v) ≤ r := by
    intro u hu
    by_contra! hn
    have huS : u ∉ S := by
      intro huS
      have hh := hn u huS
      rw [l1dist_self] at hh
      linarith
    have hnew : insert u S ∈ good := by
      apply mem_filter.mpr
      refine ⟨mem_powerset.mpr (insert_subset hu (mem_powerset.mp hSF)),?_⟩
      intro x hx y hy hxy
      rcases mem_insert.mp hx with rfl | hxS
      · rcases mem_insert.mp hy with rfl | hyS
        · exact (hxy rfl).elim
        · exact hn y hyS
      · rcases mem_insert.mp hy with rfl | hyS
        · rw [l1dist_comm]; exact hn x hxS
        · exact hsep x hxS y hyS hxy
    have hh := hmax _ hnew
    rw [card_insert_of_notMem huS] at hh
    omega
  refine ⟨S,mem_powerset.mp hSF,?_,hsep,hcover⟩
  obtain ⟨u,hu⟩ := hF
  obtain ⟨v,hv,_⟩ := hcover u hu
  exact ⟨v,hv⟩

omit [DecidableEq V] in

lemma retain_fibers (S : Finset V) (T : Finset I) (f : V → I)
    (hf : ∀u ∈ S, f u ∈ T) (w : I → ℝ) (hw : ∀i ∈ T, 0 < w i)
    {c : ℝ} (hc : 0 < c) :
    ∃J : Finset I, J ⊆ T ∧
      (∀i ∈ J, (S.filter (fun u => f u=i)).Nonempty ∧
        c*w i ≤ ((S.filter (fun u => f u=i)).card : ℝ)) ∧
      (S.card : ℝ)-c*(∑i ∈ T, w i) ≤ ∑i ∈ J, ((S.filter (fun u => f u=i)).card : ℝ) := by
  let J := T.filter (fun i => c*w i ≤ ((S.filter (fun u => f u=i)).card : ℝ))
  have hsum : (∑i ∈ T, ((S.filter (fun u => f u=i)).card : ℝ)) = S.card := by
    rw [←Nat.cast_sum]
    congr 1
    exact sum_card_fiberwise_eq_card_filter S T f |>.trans (by
      congr 1
      exact filter_eq_self.mpr hf)
  refine ⟨J,filter_subset _ _,?_,?_⟩
  · intro i hi
    obtain ⟨hi,hci⟩ := mem_filter.mp hi
    refine ⟨card_pos.mp ?_,hci⟩
    have hh := mul_pos hc (hw i hi)
    have : (0:ℝ) < (S.filter (fun u => f u=i)).card := hh.trans_le hci
    exact_mod_cast this
  · have hbound : ∑i ∈ T, ((S.filter (fun u => f u=i)).card : ℝ) ≤
        (∑i ∈ T, if i ∈ J then ((S.filter (fun u => f u=i)).card : ℝ) else 0)+c*(∑i ∈ T, w i) := by
      rw [mul_sum,←sum_add_distrib]
      apply sum_le_sum
      intro i hi
      by_cases hiJ : i ∈ J
      · rw [ite_eq_left hiJ]
        linarith [mul_pos hc (hw i hi)]
      · rw [ite_eq_right hiJ,zero_add]
        exact le_of_lt (lt_of_not_ge (fun hh => hiJ (mem_filter.mpr ⟨hi,hh⟩)))
    rw [hsum] at hbound
    have he : (∑i ∈ T, if i ∈ J then ((S.filter (fun u => f u=i)).card : ℝ) else 0) =
        ∑i ∈ J, ((S.filter (fun u => f u=i)).card : ℝ) := by
      rw [←sum_filter]
      congr 1
      exact filter_mem_eq_inter.trans (inter_eq_right.mpr (filter_subset _ _))
    rw [he] at hbound
    linarith

end
end StrongThinTree.Geometry

namespace StrongThinTree.Geometry
noncomputable section
open Finset RadialShell
open scoped Classical
variable {V : Type uV2} [DecidableEq V] {h : ℕ} {X : V → Fin h → ℝ}

lemma compact_from_net (S W : Finset V) (hS : S.Nonempty) (hW : W.Nonempty)
    {δ D : ℝ} (hδ : 0 < δ) (hD : δ ≤ D)
    (hsep : (S : Set V).Pairwise (fun u v =>
      Disjoint ((ball u δ).support X) ((ball v δ).support X)))
    (hcover : ∀u ∈ S, ∃v ∈ W, l1dist (X u) (X v) ≤ 3*D)
    (hsmall : 432*D*(W.card : ℝ) ≤ δ*(S.card : ℝ)) :
    ∃F : CompactFamily X δ (6*D),
      δ*(S.card : ℝ)/2 ≤ δ*(∑B ∈ F.bags, (B.card : ℝ)) := by
  have hD0 : 0 < D := hδ.trans_le hD
  obtain ⟨w0,hw0⟩ := hW
  have hex : ∀u : V, ∃v ∈ W, u ∈ S → l1dist (X u) (X v) ≤ 3*D := by
    intro u
    by_cases hu : u ∈ S
    · obtain ⟨v,hv,hvu⟩ := hcover u hu
      exact ⟨v,hv,fun _ => hvu⟩
    · exact ⟨w0,hw0,fun hh => (hu hh).elim⟩
  choose f hfW hfDist using hex
  let fiber := fun i => S.filter (fun u => f u=i)
  let c : ℝ := 216*D/δ
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨J,hJW,hJ,hgain⟩ := retain_fibers S W f (fun u _ => hfW u)
    (fun _ => (1:ℝ)) (fun _ _ => zero_lt_one) hc
  have hsumRet : (∑i ∈ J, ((fiber i).card : ℝ)) ≥ (S.card : ℝ)/2 := by
    have hcost : c*(W.card : ℝ) ≤ (S.card : ℝ)/2 := by
      dsimp [c]
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hδ).mpr
      nlinarith
    simp only [sum_const, nsmul_eq_mul,mul_one] at hgain
    dsimp [fiber]
    linarith
  have hJne : J.Nonempty := by
    by_contra hh
    rw [not_nonempty_iff_eq_empty.mp hh,sum_empty] at hsumRet
    have hs0 : (0:ℝ) < S.card := by exact_mod_cast card_pos.mpr hS
    linarith
  have hinj : Set.InjOn fiber J := by
    intro i hi j hj hij
    obtain ⟨u,hu⟩ := (hJ i hi).1
    have huj : u ∈ fiber j := hij ▸ hu
    exact (mem_filter.mp hu).2.symm.trans (mem_filter.mp huj).2
  have hfiber : ∀i ∈ J, fiber i ⊆ S := fun i _ => filter_subset _ _
  let F : CompactFamily X δ (6*D) := {
    bags := J.image fiber
    nonempty := hJne.image fiber
    radius_pos := hδ
    bags_disjoint := by
      intro A hA B hB hAB
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hA
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hB
      apply Finset.disjoint_left.mpr
      intro u hui huj
      have hij := (mem_filter.mp hui).2.symm.trans (mem_filter.mp huj).2
      exact hAB (congrArg fiber hij)
    balls_disjoint := by
      intro u hu v hv huv
      obtain ⟨A,hA,huA⟩ := mem_biUnion.mp hu
      obtain ⟨B,hB,hvB⟩ := mem_biUnion.mp hv
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hA
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hB
      exact hsep (hfiber i hi huA) (hfiber j hj hvB) huv
    cardinal := by
      intro A hA
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hA
      have hh := (hJ i hi).2
      have h216 : (216:ℝ) ≤ c := (le_div_iff₀ hδ).mpr (by nlinarith)
      have : (2:ℝ) ≤ (fiber i).card := by dsimp [fiber]; nlinarith
      exact_mod_cast this
    diameter := by
      intro A hA u hu v hv
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hA
      have hui := (mem_filter.mp hu).2
      have hvi := (mem_filter.mp hv).2
      have hu' := hfDist u (hfiber i hi hu)
      have hv' := hfDist v (hfiber i hi hv)
      rw [hui] at hu'
      rw [hvi,l1dist_comm (X v) (X i)] at hv'
      have htri := l1dist_triangle (X u) (X i) (X v)
      linarith
    compact := by
      intro A hA
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hA
      have hh := (hJ i hi).2
      rw [mul_one] at hh
      have hm := (div_le_iff₀ hδ).mp hh
      nlinarith }
  refine ⟨F,?_⟩
  have he : (∑B ∈ F.bags, (B.card : ℝ)) = ∑i ∈ J, ((fiber i).card : ℝ) :=
    sum_image hinj
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left hsumRet hδ.le]

end
end StrongThinTree.Geometry

namespace StrongThinTree.Geometry
noncomputable section
open Finset RadialShell
open scoped Classical
variable {V : Type uV3} {I : Type uI2} {J : Type uJ} [DecidableEq V] [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J] {h : ℕ}

lemma normalized_small_balls (X : V → Fin h → ℝ) (Y : V → EuclideanSpace ℝ J)
    (u v : I → V) (j : I → J) (hj : Function.Injective j)
    (hN : 0 < Fintype.card I) {a ε c₁ : ℝ}
    (ha : 0 < a) (hε : 0 < ε) (hε1 : ε < 1/3) (hc : 0 < c₁)
    (hdiag : ∀i, 0 ≤ (Y (u i)-Y (v i)).ofLp (j i) ∧
      c₁ ≤ ((Y (u i)-Y (v i)).ofLp (j i))^2)
    (hbound : a * Fintype.card I * (∑i, ‖Y (u i)-Y (v i)‖^2) ≤
      (∑i, (Y (u i)-Y (v i)).ofLp (j i))^2)
    (hcontract : ∀x y, ‖Y x-Y y‖^2 ≤ l1dist (X x) (X y)) :
    a ≤ 1 ∧ ∃S : Finset V, ∃δ : ℝ, 0 < δ ∧
      S ⊆ (univ.image u ∪ univ.image v) ∧ 2 ≤ S.card ∧
      ε^2*a*Fintype.card I ≤ 1024*S.card ∧
      (S.card : ℝ)*δ = a^ε*c₁*Fintype.card I/(1024/ε^2) ∧
      (S : Set V).Pairwise (fun x y =>
        Disjoint ((ball x δ).support X) ((ball y δ).support X)) := by
  let N : ℝ := Fintype.card I
  let A : ℝ := ∑i, (Y (u i)-Y (v i)).ofLp (j i)
  have hN0 : 0 < N := by dsimp [N]; exact_mod_cast hN
  have hsqrt : ∀i, Real.sqrt c₁ ≤ (Y (u i)-Y (v i)).ofLp (j i) := by
    intro i
    exact (Real.sqrt_le_iff).mpr ⟨(hdiag i).1,(hdiag i).2⟩
  have hsum : N*Real.sqrt c₁ ≤ A := by
    simpa only [sum_const,nsmul_eq_mul,card_univ,N,A] using sum_le_sum (fun i (_ : i ∈ univ) => hsqrt i)
  have hA0 : 0 < A := (mul_pos hN0 (Real.sqrt_pos.mpr hc)).trans_le hsum
  have hA2 : c₁*N^2 ≤ A^2 := by
    have hh := sq_le_sq₀ (by positivity : 0 ≤ N*Real.sqrt c₁) hA0.le |>.mpr hsum
    rw [mul_pow,Real.sq_sqrt hc.le] at hh
    nlinarith
  obtain ⟨ha1,S,r,hr,hSF,hS2,hcard,hmass,hsep⟩ :=
    StrongThinTree.Spectral.spectral_packing_coordinates Y u v j hj ha hε hε1
      (by change 0 < A^2; positivity) hbound
  have hS0 : (0:ℝ) < S.card := by exact_mod_cast (by omega : 0 < S.card)
  have he2 : 0 < ε^2 := sq_pos_of_pos hε
  have hpow : 0 < a^ε := Real.rpow_pos_of_pos ha _
  let C : ℝ := 1024/ε^2
  have hC : 0 < C := by dsimp [C]; positivity
  let w := a^ε*c₁*N/C
  let δ := w/S.card
  have hw : 0 < w := by dsimp [w]; positivity
  have hδ : 0 < δ := div_pos hw hS0
  have hwle : w ≤ (S.card : ℝ)*r := by
    have hh := mul_le_mul_of_nonneg_left hA2 (show 0 ≤ ε^2*a^ε by positivity)
    change ε^2*a^ε*A^2 ≤ 1024*N*(S.card*r) at hmass
    have hh' : ε^2*a^ε*c₁*N ≤ 1024*(S.card*r) := by
      apply (mul_le_mul_iff_right₀ hN0).mp
      nlinarith
    dsimp [w,C]
    exact (div_le_iff₀ (div_pos (by norm_num) he2)).mpr (by
      rw [←mul_div_assoc]
      apply (le_div_iff₀ he2).mpr
      nlinarith)
  have hδr : δ ≤ r := (div_le_iff₀ hS0).mpr (by nlinarith)
  refine ⟨ha1,S,δ,hδ,hSF,hS2,hcard,?_,?_⟩
  · dsimp [δ,w,C,N]
    field_simp
  · intro x hx y hy hxy
    apply distance_balls_disjoint
    have hh := hsep x hx y hy hxy
    have hh' := hcontract x y
    have hs : (Real.sqrt r)^2 = r := Real.sq_sqrt hr.le
    have hnorm := norm_nonneg (Y x-Y y)
    have hroot := Real.sqrt_nonneg r
    nlinarith

end
end StrongThinTree.Geometry

end

end OAI
