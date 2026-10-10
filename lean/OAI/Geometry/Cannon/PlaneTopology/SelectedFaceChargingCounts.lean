import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.PackingNormalizedTileBudget
import OAI.Geometry.Cannon.Modulus.ClippedRadialEnergy
import OAI.Geometry.Cannon.Modulus.PreimageCarrierPostcompose

namespace OAI

section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology CannonFaceIncidence

attribute [local instance] Classical.propDecidable
variable {X ι : Type*} [MetricSpace X] [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {H : ι → Arc ℂ} [Fintype (Faces H)]

lemma selected_face_charging_counts
    (hH : Pairwise fun i j=>Compatible (H i) (H j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (H i) ⊆ ⋃p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (H i))\{q}))
    (D : ℕ) (hdeg : ∀ v : ℂ,Nat.card {i : ι | v∈range (H i)} ≤ D)
    (e : ℂ → X) (sel : Faces H → ℂ) (hsel : ∀ d,sel d∈faceVertices H d)
    (T : Finset X) (mesh L : ℝ) (kr kc : ℕ)
    (hrow : ∀ x : X,(T.filter (fun y=>dist x y<(L+3)*mesh)).card ≤ kr)
    (hcol : ∀ x : X,Nat.card {v : ℂ | Vertex H v ∧ dist (e v) x<(L+3)*mesh} ≤ kc) :
    (∀ d : Faces H,(Finset.univ.filter (fun i : T=>dist i.val (e (sel d))<2*mesh+mesh+L*mesh)).card ≤ kr) ∧
    (∀ i : T,(Finset.univ.filter (fun d : Faces H=>dist i.val (e (sel d))<2*mesh+mesh+L*mesh)).card ≤ D*kc) := by
  classical
  have he : 2*mesh+mesh+L*mesh=(L+3)*mesh:=by ring
  constructor
  · intro d
    apply (Finset.card_le_card_of_injOn (fun i : T=>i.val) (t:=T.filter (fun y=>dist (e (sel d)) y<(L+3)*mesh))
      (by
        intro i hi
        exact Finset.mem_filter.mpr ⟨i.property,by simpa only [he,dist_comm] using (Finset.mem_filter.mp hi).2⟩)
      (fun i _ j _ hij=>Subtype.ext hij)).trans (hrow _)
  · intro i
    let S:=Finset.univ.filter (fun d : Faces H=>dist i.val (e (sel d))<2*mesh+mesh+L*mesh)
    have hImg : (S.image sel).card ≤ kc := by
      have hfin : {v : ℂ | Vertex H v ∧ dist (e v) i.val<(L+3)*mesh}.Finite:=
        (finite_vertex_set H).subset (fun _ h=>h.1)
      have hsub : (S.image sel : Set ℂ) ⊆ {v : ℂ | Vertex H v ∧ dist (e v) i.val<(L+3)*mesh} := by
        rintro v hv
        obtain ⟨d,hd,rfl⟩:=Finset.mem_image.mp hv
        refine ⟨((mem_faceVertices H d (sel d)).mp (hsel d)).1,?_⟩
        simpa only [he,dist_comm] using (Finset.mem_filter.mp hd).2
      have hh:=Nat.card_mono hfin hsub
      have hh' : (S.image sel).card ≤ Nat.card {v : ℂ | Vertex H v ∧ dist (e v) i.val<(L+3)*mesh}:=by
        simpa [Nat.card_eq_fintype_card] using hh
      exact hh'.trans (hcol _)
    apply (Finset.card_le_mul_card_image S D (f:=sel) ?_).trans (Nat.mul_le_mul_left D hImg)
    intro v hv
    apply (Finset.card_le_card (show S.filter (fun d=>sel d=v) ⊆
      Finset.univ.filter (fun d : Faces H=>v∈faceVertices H d) from ?_)).trans
        (face_incidence_card_le hH Q hQ hK D hdeg v)
    intro d hd
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    rw [←(Finset.mem_filter.mp hd).2]
    exact hsel d
end CannonEmbeddedArc.Arc

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology CannonFaceIncidence CannonTriangleWinding CannonMobius
open CannonCarrierCharging CannonCells CannonUniformization
open scoped OnePoint BigOperators

attribute [local instance] Classical.propDecidable
variable {X ι : Type*} [MetricSpace X] [LocallyPathConnectedSpace X]
  [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {H : ι → Arc ℂ} [Fintype (Faces H)]

theorem packing_radial_modulus_bound
    (hH : Pairwise fun i j=>Compatible (H i) (H j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (H i) ⊆ ⋃p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (H i))\{q}))
    (D : ℕ) (hdeg : ∀ v : ℂ,Nat.card {i : ι | v∈range (H i)} ≤ D)
    (e : ℂ → X) (he : Continuous e)
    (z : ℂ → ℂ) (ρ : ℂ → ℝ) (hρ : ∀ v,0<ρ v)
    (hlen : ∀ i,dist (z (H i 0)) (z (H i 1))=ρ (H i 0)+ρ (H i 1))
    (hsep : ∀ u,Vertex H u → ∀ v,Vertex H v → u≠v → ρ u+ρ v ≤ dist (z u) (z v))
    (hcycles : ∀ d : Faces H,∃ C : FacialCycle H d,0<area (z C.a) (z C.b) (z C.c))
    (out : Faces H)
    (hI : ∀ d e : Faces H,d≠out → e≠out → d≠e →
      Disjoint (interior (faceHull H z d)) (interior (faceHull H z e)))
    (hfill : (⋃ d : {d : Faces H // d≠out},faceHull H z d.val)=faceHull H z out)
    (pole : ℂ) (hpv : Vertex H pole)
    (N : Sphere ≃ₜ Sphere) (hN : N∈biholomorphic) (hpole : N (z pole)=∞)
    (T : Finset X) (mesh L : ℝ) (hm : 0 < mesh)
    (hcover : ∀ x : X,∃ y∈T,dist x y ≤ mesh)
    (hdiam : ∀ d,∀ x∈compactifiedFace H e d,∀ y∈compactifiedFace H e d,dist x y ≤ L*mesh)
    (kr kc : ℕ)
    (hrow : ∀ x : X,(T.filter (fun y=>dist x y<(L+3)*mesh)).card ≤ kr)
    (hcol : ∀ x : X,Nat.card {v : ℂ | Vertex H v ∧ dist (e v) x<(L+3)*mesh} ≤ kc)
    (hc : ∀ S : Set Sphere,IsPreconnected S →
      IsPreconnected (⋃(d : {d : Faces H // (S∩sphereTile H z out d).Nonempty}),compactifiedFace H e d.val))
    (F : Set (Set X)) (hFn : ∀ E∈F,E.Nonempty)
    (p : ℂ) (a b R : ℝ) (hab : a ≤ b) (hb : b ≤ R) (hR : 0 ≤ R)
    (hcross : ∀ t∈Icc a b,
      ∃ x∈⋃(d : {d : Faces H // (((↑) '' sphere p t : Set Sphere)∩N '' sphereTile H z out d).Nonempty}),compactifiedFace H e d.val,
      ∃ y∈⋃(d : {d : Faces H // (((↑) '' sphere p t : Set Sphere)∩N '' sphereTile H z out d).Nonempty}),compactifiedFace H e d.val,
        ∀ γ : Path x y,range γ∈F) :
    (b-a)^2 ≤ 36*(26*(D:ℝ)+1)*R^2*(kr:ℝ)*(D*kc:ℕ)*
      modulus (fun i : T=>ball i.val (2*mesh)) F := by
  classical
  obtain ⟨c,rad,sel,hsel,hrad,hcell,hbudget,hbad⟩:=packing_normalized_tile_budget
    hH Q hQ hK z ρ hρ hlen hsep hcycles out hI hfill pole hpv N hN hpole D hdeg
  obtain ⟨hrow',hcol'⟩:=selected_face_charging_counts hH Q hQ hK D hdeg e sel hsel T mesh L kr kc hrow hcol
  have hconn : ∀ t∈Icc a b,IsPreconnected
      (⋃(d : {d : Faces H // (((↑) '' sphere p t : Set Sphere)∩N '' sphereTile H z out d).Nonempty}),compactifiedFace H e d.val) := by
    intro t _
    exact spherical_circle_carriers_preconnected (compactifiedFace H e) (fun d=>N '' sphereTile H z out d)
      (normalized_carrier (compactifiedFace H e) (sphereTile H z out) hc N) p t
  exact clipped_spherical_carrier_modulus (compactifiedFace H e) (fun d=>N '' sphereTile H z out d)
    (fun d=>e (sel d)) (fun i : T=>i.val) mesh mesh (L*mesh) hm
    (fun d x hx=>hdiam d x hx (e (sel d)) (compactifiedFace_vertex e he (hsel d))) F hFn
    (by
      intro x
      obtain ⟨y,hy,hxy⟩:=hcover x
      refine ⟨⟨y,hy⟩,?_⟩
      change dist x y<2*mesh
      linarith)
    c rad (fun d=>pole∉faceVertices H d) hrad p hab hb hR D hcell (by
      refine le_trans (Finset.sum_le_sum (fun d _=>?_)) (hbudget p R hR)
      by_cases hd : pole∉faceVertices H d ∧ (((↑) : ℂ → Sphere) ⁻¹' (N '' sphereTile H z out d)∩closedBall p R).Nonempty <;> simp only [hd,ite_false,le_refl])
    (by
      convert hbad using 1
      congr 1
      ext d
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]) hconn hcross kr (D*kc) hrow' hcol'
end CannonEmbeddedArc.Arc

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology CannonFaceIncidence CannonTriangleWinding CannonMobius
open CannonCarrierCharging CannonCells CannonUniformization
open scoped OnePoint BigOperators

attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X] [LocallyPathConnectedSpace X]

theorem packing_relative_modulus_cost
    (LI σ : ℝ)
    (hinner : ∀ o u v : X,∀ s : ℝ,0<s → dist o u ≤ s → dist o v ≤ s →
      JoinedIn (closedBall o (LI*s)) u v)
    (houter : ∀ o u v : X,∀ s : ℝ,0<s → s ≤ dist o u → s ≤ dist o v →
      JoinedIn (ball o (σ*s))ᶜ u v) :
    ∃ V : ℝ → ℝ,(∀ ε,0<ε → 0<V ε) ∧
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι],
    ∀ (H : ι → Arc ℂ) [Fintype (Faces H)],
    Pairwise (fun i j=>Compatible (H i) (H j)) →
    ∀ (Q : Finset (ℂ × ℂ)),(∀ i,range (H i) ⊆ ⋃p∈Q,segment ℝ p.1 p.2) →
    (∀ q : ℂ,IsPreconnected ((⋃ i,range (H i))\{q})) →
    ∀ (D : ℕ),(∀ v : ℂ,Nat.card {i : ι | v∈range (H i)} ≤ D) →
    ∀ (e : ℂ → X),Continuous e →
    ∀ (z : ℂ → ℂ) (ρ : ℂ → ℝ),(∀ v,0<ρ v) →
    (∀ i,dist (z (H i 0)) (z (H i 1))=ρ (H i 0)+ρ (H i 1)) →
    (∀ u,Vertex H u → ∀ v,Vertex H v → u≠v → ρ u+ρ v ≤ dist (z u) (z v)) →
    (∀ d : Faces H,∃ C : FacialCycle H d,0<area (z C.a) (z C.b) (z C.c)) →
    ∀ (out : Faces H),
    (∀ d e : Faces H,d≠out → e≠out → d≠e →
      Disjoint (interior (faceHull H z d)) (interior (faceHull H z e))) →
    ((⋃ d : {d : Faces H // d≠out},faceHull H z d.val)=faceHull H z out) →
    ∀ (N : Sphere ≃ₜ Sphere),N∈biholomorphic →
    ∀ (T : Finset X) (mesh L : ℝ),0 < mesh →
    (∀ x : X,∃ y∈T,dist x y ≤ mesh) →
    (∀ d,∀ x∈compactifiedFace H e d,∀ y∈compactifiedFace H e d,dist x y ≤ L*mesh) →
    ∀ (kr kc : ℕ),
    (∀ x : X,(T.filter (fun y=>dist x y<(L+3)*mesh)).card ≤ kr) →
    (∀ x : X,Nat.card {v : ℂ | Vertex H v ∧ dist (e v) x<(L+3)*mesh} ≤ kc) →
    (∀ S : Set Sphere,IsPreconnected S →
      IsPreconnected (⋃(d : {d : Faces H // (S∩sphereTile H z out d).Nonempty}),compactifiedFace H e d.val)) →
    ∀ (g : C(X,Sphere)),
    (∀ S : Set Sphere,g ⁻¹' S ⊆
      ⋃(d : {d : Faces H // (S∩N '' sphereTile H z out d).Nonempty}),compactifiedFace H e d.val) →
    ∀ (v : Fin 3 → ℂ) (s : ℝ),0<s → (∀ i,Vertex H (v i)) →
      (∀ i j,i≠j → s ≤ dist (e (v i)) (e (v j))) →
      (∀ i,g (e (v i))=std i) → (∀ i,N (z (v i))=std i) →
    ∀ (o a₀ b₀ : X) (r R ε : ℝ),0<r → 0<R → R ≤ s/2 →
      dist o a₀ ≤ r → R ≤ dist o b₀ →
      0<dist (g o) (g b₀) → 0<ε →
      ε*dist (g o) (g b₀)<dist (g o) (g a₀) →
    V ε ≤ 324*(26*(D:ℝ)+1)*(kr:ℝ)*(D*kc:ℕ)*
      modulus (fun i : T=>ball i.val (2*mesh)) (annulusFamily o (LI*r) (σ*R)) := by
  obtain ⟨C,hC,hwit⟩:=relative_radial_carrier_witness
  have hCp : 0<C:=by linarith
  let η : ℝ → ℝ:=fun ε=>min 1 (ε^2/(204*C^2))
  have hηp (ε : ℝ) (hε : 0<ε) : 0<η ε:=by dsimp [η]; positivity
  refine ⟨fun ε=>(η ε)^2,fun ε hε=>sq_pos_of_pos (hηp ε hε),?_⟩
  intro ι _ _ _ H _ hH Q hQ hK D hdeg e he z ρ hρ hlen hsep hcycles out hI hfill N hN
    T mesh L hm hcover hdiam kr kc hrow hcol hc g hpre v s hs hv hvs hmark hNm
    o a₀ b₀ r R ε hr hR hRs ha₀ hb₀ hdb hε hdiff
  have hη1 : η ε ≤ 1:=min_le_left _ _
  have hηε : 102*η ε*C^2<ε^2 := by
    have hh : η ε*(204*C^2) ≤ ε^2 :=
      (le_div_iff₀ (by positivity)).mp (min_le_right 1 (ε^2/(204*C^2)))
    nlinarith [sq_pos_of_pos hε]
  obtain ⟨i,p,a,b,ha,hab,hb,hw,hcross⟩:=hwit LI σ hinner houter
    (compactifiedFace H e) (fun d=>N '' sphereTile H z out d) g hpre
    (fun i=>e (v i)) s hs hvs hmark o a₀ b₀ r R ε (η ε) hr hR hRs ha₀ hb₀ hdb hε
    (hηp ε hε).le hη1 hηε hdiff
  let NN : Sphere ≃ₜ Sphere:=N.trans (markedChart i)
  have hNN : NN∈biholomorphic := by
    change markedChart i*N∈biholomorphic
    exact biholomorphic.mul_mem (markedChart_biholomorphic i) hN
  have hNp : NN (z (v i))=∞ := by
    change markedChart i (N (z (v i)))=∞
    rw [hNm,markedChart_pole]
  let S:=C*dist (g o) (g b₀)
  have hS : 0<S:=mul_pos hCp hdb
  have hcross' : ∀ t∈Icc a b,
      ∃ x∈⋃(d : {d : Faces H // (((↑) '' sphere p t : Set Sphere)∩NN '' sphereTile H z out d).Nonempty}),compactifiedFace H e d.val,
      ∃ y∈⋃(d : {d : Faces H // (((↑) '' sphere p t : Set Sphere)∩NN '' sphereTile H z out d).Nonempty}),compactifiedFace H e d.val,
        ∀ γ : Path x y,range γ∈annulusFamily o (LI*r) (σ*R) := by
    have heq (d : Faces H) : NN '' sphereTile H z out d=markedChart i '' (N '' sphereTile H z out d) := by
      rw [image_image]
      rfl
    intro t ht
    obtain ⟨x,hx,y,hy,hpaths⟩:=hcross t ht
    have hmem (x : X)
        (hx : x∈⋃(d : {d : Faces H // (((↑) '' sphere p t : Set Sphere)∩markedChart i '' (N '' sphereTile H z out d)).Nonempty}),compactifiedFace H e d.val) :
        x∈⋃(d : {d : Faces H // (((↑) '' sphere p t : Set Sphere)∩NN '' sphereTile H z out d).Nonempty}),compactifiedFace H e d.val := by
      obtain ⟨d,hd⟩:=mem_iUnion.mp hx
      refine mem_iUnion.mpr ⟨⟨d.val,?_⟩,hd⟩
      rw [heq]
      exact d.property
    exact ⟨x,hmem x hx,y,hmem y hy,hpaths⟩
  have hbound:=packing_radial_modulus_bound hH Q hQ hK D hdeg e he z ρ hρ hlen hsep hcycles
    out hI hfill (v i) (hv i) NN hNN hNp T mesh L hm hcover hdiam kr kc hrow hcol hc
    (annulusFamily o (LI*r) (σ*R))
    (fun E hE=>by
      obtain ⟨x,y,γ,hγ,hrest⟩:=hE
      subst E
      exact ⟨x,0,γ.source⟩)
    p a b (3*S) hab hb (by positivity) hcross'
  have hh : S^2*(η ε)^2 ≤ S^2*(324*(26*(D:ℝ)+1)*(kr:ℝ)*(D*kc:ℕ)*
      modulus (fun i : T=>ball i.val (2*mesh)) (annulusFamily o (LI*r) (σ*R))) := by
    calc S^2*(η ε)^2 = (b-a)^2 := by rw [hw]; dsimp [S]; ring
         _ ≤ _ := hbound
         _ = _ := by ring
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hS)).mp (by simpa only [mul_comm] using hh)
end CannonEmbeddedArc.Arc

end
end

end OAI
