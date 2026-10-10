import Mathlib
import OAI.Combinatorics.ThinTrees.Metric.AssignedCharging

namespace OAI

/-! Metric bag extraction. -/

section

namespace AlgorithmicThinTrees.MetricProfiles.CompactGeometry
noncomputable section
open Finset
open StrongThinTree.Geometry (retain_fibers)
open scoped Classical
variable {V I : Type*} [DecidableEq V] [DecidableEq I] {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord]

omit [DecidableEq V] in
lemma distance_balls_disjoint (X : V → Coord → ℝ) (u v : V) {r : ℝ}
    (hsep : 2*r ≤ normDistance (X u) (X v)) :
    Disjoint ((RadialShell.ball u r).support X) ((RadialShell.ball v r).support X) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  have hx := normDistance_triangle (X u) z (X v)
  rw [normDistance_comm (X u) z] at hx
  have hz₁ := hz.2.1
  have hz₂ := hz'.2.1
  change normDistance z (X u) < r at hz₁
  change normDistance z (X v) < r at hz₂
  linarith

omit [PseudoMetricSpace Coord] in
lemma separated_net (X : V → Coord → ℝ) (F : Finset V) (hF : F.Nonempty)
    {r : ℝ} (hr : 0 ≤ r) :
    ∃S : Finset V, S ⊆ F ∧ S.Nonempty ∧
      (∀u ∈ S, ∀v ∈ S, u ≠ v → r < normDistance (X u) (X v)) ∧
      ∀u ∈ F, ∃v ∈ S, normDistance (X u) (X v) ≤ r := by
  let sep : Finset V → Prop := fun S => ∀u ∈ S, ∀v ∈ S, u ≠ v → r < normDistance (X u) (X v)
  let good := F.powerset.filter sep
  have hgood : good.Nonempty := ⟨∅,mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _),by simp [sep]⟩⟩
  obtain ⟨S,hS,hmax⟩ := exists_max_image good card hgood
  obtain ⟨hSF,hsep⟩ := mem_filter.mp hS
  have hcover : ∀u ∈ F, ∃v ∈ S, normDistance (X u) (X v) ≤ r := by
    intro u hu
    by_contra! hn
    have huS : u ∉ S := by
      intro huS
      have hh := hn u huS
      rw [normDistance_self] at hh
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
        · rw [normDistance_comm]; exact hn x hxS
        · exact hsep x hxS y hyS hxy
    have hh := hmax _ hnew
    rw [card_insert_of_notMem huS] at hh
    omega
  refine ⟨S,mem_powerset.mp hSF,?_,hsep,hcover⟩
  obtain ⟨u,hu⟩ := hF
  obtain ⟨v,hv,_⟩ := hcover u hu
  exact ⟨v,hv⟩

end
end AlgorithmicThinTrees.MetricProfiles.CompactGeometry

namespace AlgorithmicThinTrees.MetricProfiles.CompactGeometry
noncomputable section
open Finset
open StrongThinTree.Geometry (retain_fibers)
open RadialShell
open scoped Classical
variable {V : Type*} [DecidableEq V] {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {X : V → Coord → ℝ}

lemma compact_from_net (S W : Finset V) (hS : S.Nonempty) (hW : W.Nonempty)
    {δ D : ℝ} (hδ : 0 < δ) (hD : δ ≤ D)
    (hsep : (S : Set V).Pairwise (fun u v =>
      Disjoint ((ball u δ).support X) ((ball v δ).support X)))
    (hcover : ∀u ∈ S, ∃v ∈ W, normDistance (X u) (X v) ≤ 3*D)
    (hsmall : 432*D*(W.card : ℝ) ≤ δ*(S.card : ℝ)) :
    ∃F : CompactFamily X δ (6*D),
      δ*(S.card : ℝ)/2 ≤ δ*(∑B ∈ F.bags, (B.card : ℝ)) := by
  have hD0 : 0 < D := hδ.trans_le hD
  obtain ⟨w0,hw0⟩ := hW
  have hex : ∀u : V, ∃v ∈ W, u ∈ S → normDistance (X u) (X v) ≤ 3*D := by
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
      rw [hvi,normDistance_comm (X v) (X i)] at hv'
      have htri := normDistance_triangle (X u) (X i) (X v)
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
end AlgorithmicThinTrees.MetricProfiles.CompactGeometry

namespace AlgorithmicThinTrees.MetricProfiles.CompactGeometry
noncomputable section
open Finset
open StrongThinTree.Geometry (retain_fibers)
open RadialShell
open scoped Classical
variable {V I J : Type*} [DecidableEq V] [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J] {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord]

lemma normalized_small_balls (X : V → Coord → ℝ) (Y : V → EuclideanSpace ℝ J)
    (u v : I → V) (j : I → J) (hj : Function.Injective j)
    (hN : 0 < Fintype.card I) {a ε c₁ : ℝ}
    (ha : 0 < a) (hε : 0 < ε) (hε1 : ε < 1/3) (hc : 0 < c₁)
    (hdiag : ∀i, 0 ≤ (Y (u i)-Y (v i)).ofLp (j i) ∧
      c₁ ≤ ((Y (u i)-Y (v i)).ofLp (j i))^2)
    (hbound : a * Fintype.card I * (∑i, ‖Y (u i)-Y (v i)‖^2) ≤
      (∑i, (Y (u i)-Y (v i)).ofLp (j i))^2)
    (hcontract : ∀x y, ‖Y x-Y y‖^2 ≤ normDistance (X x) (X y)) :
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
end AlgorithmicThinTrees.MetricProfiles.CompactGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell
open StrongThinTree.Geometry (retain_fibers)
open scoped Classical
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Doubled Coord → ℝ}

lemma assigned_from_net (T : Finset (Finset (Fin n))) (W : Finset (Fin n))
    (hW : W.Nonempty) (hT : T ⊆ H.nodes) (hroot : ∀t ∈ T, t ≠ univ)
    (hboundary : ∀t ∈ T, 0 < (parentBoundary H G t).card)
    {D η : ℝ} (hD : 0 < D)
    (hsep : (W : Set (Fin n)).Pairwise (fun u v =>
      Disjoint ((ball u D).support X) ((ball v D).support X)))
    (hcenter : ∀u ∈ W, ∃t ∈ T, u ∈ t ∧ ∃e ∈ parentBoundary H G t,
      (G.left e = u ∨ G.right e = u) ∧ normDistance (X (G.left e)) (X (G.right e)) < D)
    (hη : η ≤ (W.card : ℝ)/(2*(∑t ∈ T, ((parentBoundary H G t).card : ℝ)))) :
    ∃F : AssignedFamily H G X η, F.radius = D ∧ F.owners ⊆ T ∧
      D*(W.card : ℝ)/2 ≤ F.mass := by
  obtain ⟨u0,hu0⟩ := hW
  obtain ⟨t0,ht0,ht0c⟩ := hcenter u0 hu0
  have hex : ∀u : Fin n, ∃t ∈ T, u ∈ W → u ∈ t ∧ ∃e ∈ parentBoundary H G t,
      (G.left e = u ∨ G.right e = u) ∧ normDistance (X (G.left e)) (X (G.right e)) < D := by
    intro u
    by_cases hu : u ∈ W
    · obtain ⟨t,ht,hc⟩ := hcenter u hu
      exact ⟨t,ht,fun _ => hc⟩
    · exact ⟨t0,ht0,fun hh => (hu hh).elim⟩
  choose f hfT hf using hex
  let N : ℝ := ∑t ∈ T, ((parentBoundary H G t).card : ℝ)
  have hN : 0 < N := sum_pos (fun t ht => by exact_mod_cast hboundary t ht) ⟨t0,ht0⟩
  have hW0 : (0:ℝ) < W.card := by exact_mod_cast card_pos.mpr ⟨u0,hu0⟩
  let c : ℝ := W.card/(2*N)
  have hc : 0 < c := div_pos hW0 (mul_pos (by norm_num) hN)
  obtain ⟨J,hJT,hJ,hgain⟩ := retain_fibers W T f (fun u _ => hfT u)
    (fun t => ((parentBoundary H G t).card : ℝ))
    (fun t ht => by exact_mod_cast hboundary t ht) hc
  let fiber := fun t => W.filter (fun u => f u=t)
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let a (t : J) : AssignedBag H G X D η := {
    owner := t.val
    owner_mem := hT (hJT t.property)
    nonroot := hroot t.val (hJT t.property)
    centers := fiber t.val
    nonempty := (hJ t.val t.property).1
    radius_pos := hD
    disjoint := hsep.mono (filter_subset _ _)
    assignment := (mul_le_mul_of_nonneg_right hη (Nat.cast_nonneg _)).trans (hJ t.val t.property).2
    endpoint := by
      intro u hu
      obtain ⟨hu,hfu⟩ := mem_filter.mp hu
      simpa only [hfu] using hf u hu }
  let F : AssignedFamily H G X η := {
    radius := D
    positive := hD
    count := Fintype.card J
    bag := fun i => a (e i)
    owner_injective := by
      intro i j hij
      exact e.injective (Subtype.ext hij)
    separated := by
      intro i u hu j v hv hne
      apply hsep (mem_filter.mp hu).1 (mem_filter.mp hv).1
      intro huv
      subst v
      have hh : (e i).val = (e j).val :=
        (mem_filter.mp hu).2.symm.trans (mem_filter.mp hv).2
      rcases hne with hne | hne
      · exact hne (e.injective (Subtype.ext hh))
      · exact hne rfl }
  have hsum : (∑i : Fin F.count, ((F.bag i).centers.card : ℝ)) =
      ∑t ∈ J, ((fiber t).card : ℝ) := by
    change (∑i : Fin (Fintype.card J), ((fiber (e i).val).card : ℝ)) = _
    rw [e.sum_comp (fun t : J => ((fiber t.val).card : ℝ))]
    exact sum_coe_sort J (fun t => ((fiber t).card : ℝ))
  refine ⟨F,rfl,?_,?_⟩
  · intro t ht
    obtain ⟨i,hi,rfl⟩ := mem_image.mp ht
    exact hJT (e i).property
  · have heq : c*N = (W.card : ℝ)/2 := by dsimp [c]; field_simp
    change (W.card : ℝ)-c*N ≤ _ at hgain
    rw [heq] at hgain
    change D*(W.card : ℝ)/2 ≤ (∑i : Fin F.count, ((F.bag i).centers.card : ℝ))*D
    rw [hsum]
    have hh := mul_le_mul_of_nonneg_left hgain hD.le
    nlinarith

end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell
open StrongThinTree.Geometry (retain_fibers)
open scoped Classical
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Doubled Coord → ℝ}

lemma capture_small_balls (T : Finset (Finset (Fin n))) (S P : Finset (Fin n))
    (hS : S.Nonempty) (hT : T ⊆ H.nodes) (hroot : ∀t ∈ T, t ≠ univ)
    (hboundary : ∀t ∈ T, 0 < (parentBoundary H G t).card)
    {δ c₂ η : ℝ} (hδ : 0 < δ) (hc : 0 < c₂) (_hη : 0 ≤ η)
    (hsep : (S : Set (Fin n)).Pairwise (fun u v =>
      Disjoint ((ball u δ).support X) ((ball v δ).support X)))
    (hcover : ∀u ∈ S, ∃v ∈ P, normDistance (X u) (X v) ≤ c₂)
    (hP : ∀u ∈ P, ∃t ∈ T, u ∈ t ∧ ∃e ∈ parentBoundary H G t,
      (G.left e = u ∨ G.right e = u) ∧ normDistance (X (G.left e)) (X (G.right e)) ≤ c₂)
    (hηδ : 864*η*(∑t ∈ T, ((parentBoundary H G t).card : ℝ)) ≤ S.card)
    (hηc : 1728*η*c₂*(∑t ∈ T, ((parentBoundary H G t).card : ℝ)) ≤ δ*S.card) :
    (∃F : CompactFamily X δ (6*max δ (2*c₂)),
      δ*(S.card : ℝ)/864 ≤ δ*(∑B ∈ F.bags, (B.card : ℝ))) ∨
    (∃F : AssignedFamily H G X η, F.radius = max δ (2*c₂) ∧ F.owners ⊆ T ∧
      δ*(S.card : ℝ)/864 ≤ F.mass) := by
  let D := max δ (2*c₂)
  have hD : 0 < D := hδ.trans_le (le_max_left _ _)
  have hcD : c₂ < D := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  obtain ⟨u0,hu0⟩ := hS
  obtain ⟨v0,hv0,hv0d⟩ := hcover u0 hu0
  have hPne : P.Nonempty := ⟨v0,hv0⟩
  obtain ⟨W,hWP,hW,hWsep,hWcover⟩ := separated_net X P hPne (show 0 ≤ 2*D by positivity)
  have hballs : (W : Set (Fin n)).Pairwise (fun u v =>
      Disjoint ((ball u D).support X) ((ball v D).support X)) := by
    intro u hu v hv huv
    exact distance_balls_disjoint X u v (hWsep u hu v hv huv).le
  have hcover' : ∀u ∈ S, ∃v ∈ W, normDistance (X u) (X v) ≤ 3*D := by
    intro u hu
    obtain ⟨p,hp,hup⟩ := hcover u hu
    obtain ⟨v,hv,hpv⟩ := hWcover p hp
    exact ⟨v,hv,(normDistance_triangle (X u) (X p) (X v)).trans (by linarith)⟩
  by_cases hsmall : 432*D*(W.card : ℝ) ≤ δ*(S.card : ℝ)
  · obtain ⟨F,hF⟩ := compact_from_net S W ⟨u0,hu0⟩ hW hδ (le_max_left _ _) hsep hcover' hsmall
    exact Or.inl ⟨F,(by nlinarith [show (0:ℝ) ≤ S.card from Nat.cast_nonneg _] : δ*(S.card : ℝ)/864 ≤ δ*(S.card : ℝ)/2).trans hF⟩
  · have hlarge : δ*(S.card : ℝ) < 432*D*(W.card : ℝ) := lt_of_not_ge hsmall
    have hcenter : ∀u ∈ W, ∃t ∈ T, u ∈ t ∧ ∃e ∈ parentBoundary H G t,
        (G.left e = u ∨ G.right e = u) ∧ normDistance (X (G.left e)) (X (G.right e)) < D := by
      intro u hu
      obtain ⟨t,ht,hut,e,he,heu,hlen⟩ := hP u (hWP hu)
      exact ⟨t,ht,hut,e,he,heu,hlen.trans_lt hcD⟩
    let N : ℝ := ∑t ∈ T, ((parentBoundary H G t).card : ℝ)
    obtain ⟨t0,ht0,ht0c⟩ := hP v0 hv0
    have hN : 0 < N := sum_pos (fun t ht => by exact_mod_cast hboundary t ht) ⟨t0,ht0⟩
    have hnumer : 864*η*N*D ≤ δ*(S.card : ℝ) := by
      rcases le_total δ (2*c₂) with hh | hh
      · dsimp [D]
        rw [max_eq_right hh]
        change 1728*η*c₂*N ≤ δ*(S.card : ℝ) at hηc
        nlinarith
      · dsimp [D]
        rw [max_eq_left hh]
        change 864*η*N ≤ (S.card : ℝ) at hηδ
        simpa [mul_comm δ] using mul_le_mul_of_nonneg_right hηδ hδ.le
    have hassign : η ≤ (W.card : ℝ)/(2*N) := by
      apply (le_div_iff₀ (mul_pos (by norm_num) hN)).mpr
      nlinarith
    obtain ⟨F,hFD,hFT,hgain⟩ := assigned_from_net T W hW hT hroot hboundary hD hballs hcenter hassign
    exact Or.inr ⟨F,hFD,hFT,(by nlinarith : δ*(S.card : ℝ)/864 ≤ D*(W.card : ℝ)/2).trans hgain⟩

end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell
open StrongThinTree.Geometry (retain_fibers)
open scoped Classical
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Doubled Coord → ℝ}

lemma density_spectral_input {I : Type*} [Fintype I]
    (a d : I → ℝ) {c₁ c₂ α : ℝ}
    (hc₁ : 0 ≤ c₁) (hα : 0 ≤ α) (ha : ∀i, 0 ≤ a i)
    (hmin : ∀i, c₁ ≤ (a i)^2) (hd : ∀i, d i ≤ c₂)
    (hscale : α*c₂ ≤ c₁) :
    α*(Fintype.card I : ℝ)*(∑i, d i) ≤ (∑i, a i)^2 := by
  have hN : (0:ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
  have hsum : (Fintype.card I : ℝ)*Real.sqrt c₁ ≤ ∑i, a i := by
    simpa only [sum_const,nsmul_eq_mul,card_univ] using
      sum_le_sum (fun i (_ : i ∈ univ) => Real.sqrt_le_iff.mpr ⟨ha i,hmin i⟩)
  have hsum0 : 0 ≤ ∑i, a i := sum_nonneg (fun i _ => ha i)
  have hsum2 : c₁*(Fintype.card I : ℝ)^2 ≤ (∑i, a i)^2 := by
    have hh := (sq_le_sq₀ (mul_nonneg hN (Real.sqrt_nonneg _)) hsum0).mpr hsum
    rw [mul_pow,Real.sq_sqrt hc₁] at hh
    nlinarith only [hh]
  have hdsum : (∑i, d i) ≤ (Fintype.card I : ℝ)*c₂ := by
    simpa only [sum_const,nsmul_eq_mul,card_univ] using sum_le_sum (fun i (_ : i ∈ univ) => hd i)
  have h1 := mul_le_mul_of_nonneg_left hdsum (mul_nonneg hα hN)
  have h2 := mul_le_mul_of_nonneg_right hscale (sq_nonneg (Fintype.card I : ℝ))
  nlinarith only [h1,h2,hsum2]

lemma homogeneous_family (T : Finset (Finset (Fin n))) (F : Finset (Fin n) → Finset (Fin m))
    (Y : Fin n → EuclideanSpace ℝ (Fin m))
    (hTne : T.Nonempty) (hT : T ⊆ H.nodes) (hroot : ∀t ∈ T, t ≠ univ)
    (hF : ∀t ∈ T, F t ⊆ parentBoundary H G t) (hFn : ∀t ∈ T, (F t).Nonempty)
    {α γ ε c₁ c₂ : ℝ} (hα : 0 < α) (hγ : 0 < γ)
    (he : 0 < ε) (he1 : ε < 1/3) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hcontract : ∀u v, ‖Y u-Y v‖^2 ≤ normDistance (X u) (X v))
    (hpositive : ∀e, 0 ≤ (Y (G.left e)-Y (G.right e)).ofLp e)
    (hmin : ∀t ∈ T, ∀e ∈ F t, c₁ ≤ ((Y (G.left e)-Y (G.right e)).ofLp e)^2)
    (hmax : ∀t ∈ T, ∀e ∈ F t, ((Y (G.left e)-Y (G.right e)).ofLp e)^2 ≤ 4*c₁)
    (hdmin : ∀t ∈ T, ∀e ∈ F t, c₂/4 ≤ normDistance (X (G.left e)) (X (G.right e)))
    (hdmax : ∀t ∈ T, ∀e ∈ F t, normDistance (X (G.left e)) (X (G.right e)) ≤ c₂)
    (hbad : ∀t ∈ T, α*((parentBoundary H G t).card : ℝ)*
      (∑e ∈ parentBoundary H G t, normDistance (X (G.left e)) (X (G.right e))) ≤
      (∑e ∈ parentBoundary H G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2)
    (hdom : ∀t ∈ T, γ*(∑e ∈ parentBoundary H G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2 ≤
      (∑e ∈ F t, (Y (G.left e)-Y (G.right e)).ofLp e)^2)
    (hsmall : (α*γ/32)^ε ≤ 1/(1728*(1024/ε^2))) :
    let s := α*γ/32
    let R := ∑t ∈ T, (∑e ∈ F t, (Y (G.left e)-Y (G.right e)).ofLp e)^2/
      ((parentBoundary H G t).card : ℝ)
    (∃δ Δ : ℝ, ∃B : CompactFamily X δ Δ,
      s*c₁ ≤ δ ∧ Δ ≤ 12*c₁/s ∧ s^ε*R/(6912*(1024/ε^2)) ≤ δ*(∑D ∈ B.bags, (D.card : ℝ))) ∨
    (∃B : AssignedFamily H G X (s^(1+2*ε)), B.owners ⊆ T ∧
      s*c₁ ≤ B.radius ∧ B.radius ≤ 12*c₁/s ∧ s^ε*R/(6912*(1024/ε^2)) ≤ B.mass) := by
  let a : Fin m → ℝ := fun e => (Y (G.left e)-Y (G.right e)).ofLp e
  let d : Fin m → ℝ := fun e => normDistance (X (G.left e)) (X (G.right e))
  let E := T.biUnion F
  let N : ℝ := ∑t ∈ T, ((parentBoundary H G t).card : ℝ)
  let N' : ℝ := E.card
  let s := α*γ/32
  let C : ℝ := 1024/ε^2
  let R := ∑t ∈ T, (∑e ∈ F t, a e)^2/((parentBoundary H G t).card : ℝ)
  have hs : 0 < s := by dsimp [s]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hEn : E.Nonempty := by
    obtain ⟨t,ht⟩ := hTne
    obtain ⟨e,he⟩ := hFn t ht
    exact ⟨e,mem_biUnion.mpr ⟨t,ht,he⟩⟩
  have hN' : 0 < N' := by dsimp [N']; exact_mod_cast card_pos.mpr hEn
  have hboundary : ∀t ∈ T, 0 < (parentBoundary H G t).card :=
    fun t ht => card_pos.mpr ((hFn t ht).mono (hF t ht))
  have hN : 0 < N := by
    apply sum_pos (fun t ht => ?_) hTne
    exact_mod_cast hboundary t ht
  have hNle : N' ≤ N := by
    have h1 : E.card ≤ ∑t ∈ T, (F t).card := card_biUnion_le
    have h2 : (∑t ∈ T, (F t).card) ≤ ∑t ∈ T, (parentBoundary H G t).card :=
      sum_le_sum (fun t ht => card_le_card (hF t ht))
    dsimp [N',N]
    exact_mod_cast h1.trans h2
  have hd0 : ∀e, 0 ≤ d e := fun e => normDistance_nonneg _ _
  obtain ⟨hdensity,hR⟩ := StrongThinTree.BagDensity.family_density T (parentBoundary H G) F a d
    hα hγ hc₁.le hF hFn (fun t ht e he => hd0 e) hmax hdmin hbad hdom
    (H.subset_boundary_multiplicity G T hT hroot F hF)
  change s*N*c₂ ≤ c₁*N' at hdensity
  change R ≤ 8*c₁*N' at hR
  let specα := s*N/N'
  have ha0 : 0 < specα := div_pos (mul_pos hs hN) hN'
  have hscale : specα*N' = s*N := div_mul_cancel₀ _ hN'.ne'
  have has : s ≤ specα := by
    apply (le_div_iff₀ hN').mpr
    exact mul_le_mul_of_nonneg_left hNle hs.le
  have had : specα*c₂ ≤ c₁ := by
    change (s*N/N')*c₂ ≤ c₁
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hN').mpr hdensity
  have hminE : ∀e ∈ E, c₁ ≤ (a e)^2 := by
    intro e he
    obtain ⟨t,ht,he⟩ := mem_biUnion.mp he
    exact hmin t ht e he
  have hmaxE : ∀e ∈ E, d e ≤ c₂ := by
    intro e he
    obtain ⟨t,ht,he⟩ := mem_biUnion.mp he
    exact hdmax t ht e he
  let u : E → Fin n := fun e => G.left e.val
  let v : E → Fin n := fun e => G.right e.val
  have hIE : Fintype.card E = E.card := Fintype.card_coe E
  have hI : 0 < Fintype.card E := by rw [hIE]; exact card_pos.mpr hEn
  have hbnd : specα*(Fintype.card E : ℝ)*(∑e : E, ‖Y (u e)-Y (v e)‖^2) ≤
      (∑e : E, (Y (u e)-Y (v e)).ofLp e.val)^2 :=
    density_spectral_input (fun e : E => a e.val) (fun e : E => ‖Y (u e)-Y (v e)‖^2)
      hc₁.le ha0.le (fun e => hpositive e.val) (fun e => hminE e.val e.property)
      (fun e => (hcontract (u e) (v e)).trans (hmaxE e.val e.property)) had
  obtain ⟨ha1,S,δ,hδ,hSE,hS2,hSc,hmass,hsep⟩ := normalized_small_balls X Y u v
    (fun e : E => e.val) Subtype.val_injective hI ha0 he he1 hc₁
    (fun e => ⟨hpositive e.val,hminE e.val e.property⟩) hbnd hcontract
  have hS : S.Nonempty := card_pos.mp (by omega)
  have hSc0 : (0:ℝ) < S.card := by exact_mod_cast (by omega : 0 < S.card)
  have hcard : specα*N'/C ≤ (S.card : ℝ) := by
    apply (div_le_iff₀ hC).mpr
    dsimp [C]
    rw [←mul_div_assoc]
    apply (le_div_iff₀ (sq_pos_of_pos he)).mpr
    rw [hIE] at hSc
    change ε^2*specα*N' ≤ _ at hSc
    nlinarith only [hSc]
  have hcard₂ : (S.card : ℝ) ≤ 2*N' := by
    have hh := card_le_card hSE
    have h1 := card_union_le (univ.image u) (univ.image v)
    have h2 := card_image_le (f := u) (s := univ)
    have h3 := card_image_le (f := v) (s := univ)
    simp only [card_univ,hIE] at h2 h3
    have hSc : S.card ≤ 2*E.card := by omega
    dsimp [N']; exact_mod_cast hSc
  rw [hIE] at hmass
  change (S.card : ℝ)*δ = specα^ε*c₁*N'/C at hmass
  obtain ⟨hηδ,hηc,hlower,hupper,hgain⟩ := StrongThinTree.CaptureNumeric.thresholds
    hs has ha1 he (by linarith : ε ≤ 1/2) hC hN hN' hNle hc₁ hc₂ hSc0 hδ
    hscale hdensity hcard hcard₂ hmass hsmall hR
  let P := T.biUnion (fun t => t.filter (fun w => ∃e ∈ F t, G.left e=w ∨ G.right e=w))
  have hP : ∀w ∈ P, ∃t ∈ T, w ∈ t ∧ ∃e ∈ parentBoundary H G t,
      (G.left e=w ∨ G.right e=w) ∧ normDistance (X (G.left e)) (X (G.right e)) ≤ c₂ := by
    intro w hw
    obtain ⟨t,ht,hw⟩ := mem_biUnion.mp hw
    obtain ⟨hwt,e,he,hew⟩ := mem_filter.mp hw
    exact ⟨t,ht,hwt,e,hF t ht he,hew,hdmax t ht e he⟩
  have hEnd : ∀e ∈ E, ∃w ∈ P, (G.left e=w ∨ G.right e=w) := by
    intro e he
    obtain ⟨t,ht,het⟩ := mem_biUnion.mp he
    have hc := (mem_filter.mp (hF t ht het)).2
    rcases hc with hc | hc
    · exact ⟨G.left e,mem_biUnion.mpr ⟨t,ht,mem_filter.mpr ⟨hc.1,e,het,Or.inl rfl⟩⟩,Or.inl rfl⟩
    · exact ⟨G.right e,mem_biUnion.mpr ⟨t,ht,mem_filter.mpr ⟨hc.1,e,het,Or.inr rfl⟩⟩,Or.inr rfl⟩
  have hcover : ∀w ∈ S, ∃p ∈ P, normDistance (X w) (X p) ≤ c₂ := by
    intro w hw
    rcases mem_union.mp (hSE hw) with hw | hw
    · obtain ⟨e,he,rfl⟩ := mem_image.mp hw
      obtain ⟨p,hp,hp'⟩ := hEnd e.val e.property
      refine ⟨p,hp,?_⟩
      rcases hp' with hp' | hp'
      · simpa [u,hp',normDistance_self] using hc₂.le
      · simpa [u,d,hp'] using hmaxE e.val e.property
    · obtain ⟨e,he,rfl⟩ := mem_image.mp hw
      obtain ⟨p,hp,hp'⟩ := hEnd e.val e.property
      refine ⟨p,hp,?_⟩
      rcases hp' with hp' | hp'
      · simpa [v,d,hp',normDistance_comm] using hmaxE e.val e.property
      · simpa [v,hp',normDistance_self] using hc₂.le
  have hNcast : ∑t ∈ T, ((parentBoundary H G t).card : ℝ) = N := rfl
  have hη : 0 ≤ s^(1+2*ε) := (Real.rpow_pos_of_pos hs _).le
  obtain hcomp | hass := capture_small_balls T S P hS hT hroot hboundary hδ hc₂ hη
    hsep hcover hP hηδ hηc
  · obtain ⟨B,hB⟩ := hcomp
    refine Or.inl ⟨δ,6*max δ (2*c₂),B,hlower,?_,hgain.trans hB⟩
    change 6*max δ (2*c₂) ≤ 12*c₁/s
    calc
      _ ≤ 6*(2*c₁/s) := mul_le_mul_of_nonneg_left hupper (by norm_num)
      _ = 12*c₁/s := by ring
  · obtain ⟨B,hBD,hBT,hB⟩ := hass
    refine Or.inr ⟨B,hBT,?_,?_,hgain.trans hB⟩
    · rw [hBD]
      exact hlower.trans (le_max_left _ _)
    · rw [hBD]
      have hh : 0 ≤ c₁/s := by positivity
      calc
        max δ (2*c₂) ≤ 2*c₁/s := hupper
        _ ≤ 12*c₁/s := by rw [mul_div_assoc,mul_div_assoc]; linarith only [hh]

end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

end

end OAI
