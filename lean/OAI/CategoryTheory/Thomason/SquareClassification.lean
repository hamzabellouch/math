import Mathlib
import OAI.CategoryTheory.Thomason.GraySquares

namespace OAI

/-! Square Classification. -/

noncomputable section
universe u v w z


namespace Thomason.GrayTwo

lemma eq_code_0 (x : Coordinates) (hx : x.IsValid)
    (hs : x.vertex false 0 = 1) (ht : x.vertex true 0 = 1)
    : x = code 0 := by
  have vs := vertex_0 x hx false hs
  have vt := vertex_0 x hx true ht
  have Hv : x.vertex = (code 0).vertex := by
    funext b
    cases b
    · exact vs
    · exact vt
  rcases hx with ⟨hv, he, hf, hm, ha, hb, hc, hd⟩
  simp only [Bool.forall_bool, forall_fin4, forall_fin6] at he hf hb hc
  norm_num [vs, vt, Matrix.cons_val_two, Matrix.cons_val_three] at hb
  clear hv ha hs ht vs vt
  have He : x.edge = (code 0).edge := by
    simp only [funext_iff, Bool.forall_bool, forall_fin6]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec_val_five]
    repeat' constructor <;> omega
  norm_num [He, code, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, vec_val_five] at hc
  have Hf : x.face = (code 0).face := by
    simp only [funext_iff, Bool.forall_bool, forall_fin4]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three]
    repeat' constructor <;> omega
  apply Coordinates.ext Hv He Hf
  norm_num [Hf, code, Matrix.cons_val_two, Matrix.cons_val_three] at hd ⊢
  omega

lemma eq_code_1 (x : Coordinates) (hx : x.IsValid)
    (hs : x.vertex false 0 = 1) (ht : x.vertex true 1 = 1)
    (h0 : x.edge false 0 = 0)
    : x = code 1 := by
  have vs := vertex_0 x hx false hs
  have vt := vertex_1 x hx true ht
  have Hv : x.vertex = (code 1).vertex := by
    funext b
    cases b
    · exact vs
    · exact vt
  rcases hx with ⟨hv, he, hf, hm, ha, hb, hc, hd⟩
  simp only [Bool.forall_bool, forall_fin4, forall_fin6] at he hf hb hc
  norm_num [vs, vt, Matrix.cons_val_two, Matrix.cons_val_three] at hb
  clear hv ha hs ht vs vt
  have He : x.edge = (code 1).edge := by
    simp only [funext_iff, Bool.forall_bool, forall_fin6]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec_val_five]
    repeat' constructor <;> omega
  norm_num [He, code, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, vec_val_five] at hc
  have Hf : x.face = (code 1).face := by
    simp only [funext_iff, Bool.forall_bool, forall_fin4]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three]
    repeat' constructor <;> omega
  apply Coordinates.ext Hv He Hf
  norm_num [Hf, code, Matrix.cons_val_two, Matrix.cons_val_three] at hd ⊢
  omega

lemma eq_code_2 (x : Coordinates) (hx : x.IsValid)
    (hs : x.vertex false 0 = 1) (ht : x.vertex true 1 = 1)
    (_h0 : x.edge false 0 ≠ 0) (h1 : x.face false 0 ≠ 0)
    : x = code 2 := by
  have vs := vertex_0 x hx false hs
  have vt := vertex_1 x hx true ht
  have Hv : x.vertex = (code 2).vertex := by
    funext b
    cases b
    · exact vs
    · exact vt
  rcases hx with ⟨hv, he, hf, hm, ha, hb, hc, hd⟩
  simp only [Bool.forall_bool, forall_fin4, forall_fin6] at he hf hb hc
  norm_num [vs, vt, Matrix.cons_val_two, Matrix.cons_val_three] at hb
  clear hv ha hs ht vs vt
  have He : x.edge = (code 2).edge := by
    simp only [funext_iff, Bool.forall_bool, forall_fin6]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec_val_five]
    repeat' constructor <;> omega
  norm_num [He, code, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, vec_val_five] at hc
  have Hf : x.face = (code 2).face := by
    simp only [funext_iff, Bool.forall_bool, forall_fin4]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three]
    repeat' constructor <;> omega
  apply Coordinates.ext Hv He Hf
  norm_num [Hf, code, Matrix.cons_val_two, Matrix.cons_val_three] at hd ⊢
  omega

lemma eq_code_3 (x : Coordinates) (hx : x.IsValid)
    (hs : x.vertex false 0 = 1) (ht : x.vertex true 1 = 1)
    (h0 : x.edge false 0 ≠ 0) (h1 : x.face false 0 = 0)
    : x = code 3 := by
  have vs := vertex_0 x hx false hs
  have vt := vertex_1 x hx true ht
  have Hv : x.vertex = (code 3).vertex := by
    funext b
    cases b
    · exact vs
    · exact vt
  rcases hx with ⟨hv, he, hf, hm, ha, hb, hc, hd⟩
  simp only [Bool.forall_bool, forall_fin4, forall_fin6] at he hf hb hc
  norm_num [vs, vt, Matrix.cons_val_two, Matrix.cons_val_three] at hb
  clear hv ha hs ht vs vt
  have He : x.edge = (code 3).edge := by
    simp only [funext_iff, Bool.forall_bool, forall_fin6]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec_val_five]
    repeat' constructor <;> omega
  norm_num [He, code, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, vec_val_five] at hc
  have Hf : x.face = (code 3).face := by
    simp only [funext_iff, Bool.forall_bool, forall_fin4]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three]
    repeat' constructor <;> omega
  apply Coordinates.ext Hv He Hf
  norm_num [Hf, code, Matrix.cons_val_two, Matrix.cons_val_three] at hd ⊢
  omega

lemma eq_code_4 (x : Coordinates) (hx : x.IsValid)
    (hs : x.vertex false 0 = 1) (ht : x.vertex true 2 = 1)
    : x = code 4 := by
  have vs := vertex_0 x hx false hs
  have vt := vertex_2 x hx true ht
  have Hv : x.vertex = (code 4).vertex := by
    funext b
    cases b
    · exact vs
    · exact vt
  rcases hx with ⟨hv, he, hf, hm, ha, hb, hc, hd⟩
  simp only [Bool.forall_bool, forall_fin4, forall_fin6] at he hf hb hc
  norm_num [vs, vt, Matrix.cons_val_two, Matrix.cons_val_three] at hb
  clear hv ha hs ht vs vt
  have He : x.edge = (code 4).edge := by
    simp only [funext_iff, Bool.forall_bool, forall_fin6]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec_val_five]
    repeat' constructor <;> omega
  norm_num [He, code, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, vec_val_five] at hc
  have Hf : x.face = (code 4).face := by
    simp only [funext_iff, Bool.forall_bool, forall_fin4]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three]
    repeat' constructor <;> omega
  apply Coordinates.ext Hv He Hf
  norm_num [Hf, code, Matrix.cons_val_two, Matrix.cons_val_three] at hd ⊢
  omega

lemma eq_code_5 (x : Coordinates) (hx : x.IsValid)
    (hs : x.vertex false 0 = 1) (ht : x.vertex true 3 = 1)
    (h0 : x.edge false 3 = 1) (h1 : x.face false 3 = 0)
    : x = code 5 := by
  have vs := vertex_0 x hx false hs
  have vt := vertex_3 x hx true ht
  have Hv : x.vertex = (code 5).vertex := by
    funext b
    cases b
    · exact vs
    · exact vt
  rcases hx with ⟨hv, he, hf, hm, ha, hb, hc, hd⟩
  simp only [Bool.forall_bool, forall_fin4, forall_fin6] at he hf hb hc
  norm_num [vs, vt, Matrix.cons_val_two, Matrix.cons_val_three] at hb
  clear hv ha hs ht vs vt
  have He : x.edge = (code 5).edge := by
    simp only [funext_iff, Bool.forall_bool, forall_fin6]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec_val_five]
    repeat' constructor <;> omega
  norm_num [He, code, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, vec_val_five] at hc
  have Hf : x.face = (code 5).face := by
    simp only [funext_iff, Bool.forall_bool, forall_fin4]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three]
    repeat' constructor <;> omega
  apply Coordinates.ext Hv He Hf
  norm_num [Hf, code, Matrix.cons_val_two, Matrix.cons_val_three] at hd ⊢
  omega

lemma eq_code_6 (x : Coordinates) (hx : x.IsValid)
    (hs : x.vertex false 0 = 1) (ht : x.vertex true 3 = 1)
    (h0 : x.edge false 3 = 1) (h1 : x.face false 3 ≠ 0)
    : x = code 6 := by
  have vs := vertex_0 x hx false hs
  have vt := vertex_3 x hx true ht
  have Hv : x.vertex = (code 6).vertex := by
    funext b
    cases b
    · exact vs
    · exact vt
  rcases hx with ⟨hv, he, hf, hm, ha, hb, hc, hd⟩
  simp only [Bool.forall_bool, forall_fin4, forall_fin6] at he hf hb hc
  norm_num [vs, vt, Matrix.cons_val_two, Matrix.cons_val_three] at hb
  clear hv ha hs ht vs vt
  have He : x.edge = (code 6).edge := by
    simp only [funext_iff, Bool.forall_bool, forall_fin6]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec_val_five]
    repeat' constructor <;> omega
  norm_num [He, code, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, vec_val_five] at hc
  have Hf : x.face = (code 6).face := by
    simp only [funext_iff, Bool.forall_bool, forall_fin4]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three]
    repeat' constructor <;> omega
  apply Coordinates.ext Hv He Hf
  norm_num [Hf, code, Matrix.cons_val_two, Matrix.cons_val_three] at hd ⊢
  omega

lemma eq_code_7 (x : Coordinates) (hx : x.IsValid)
    (hs : x.vertex false 0 = 1) (ht : x.vertex true 3 = 1)
    (h0 : x.edge false 2 = 1) (h1 : x.edge true 3 = 1)
    : x = code 7 := by
  have vs := vertex_0 x hx false hs
  have vt := vertex_3 x hx true ht
  have Hv : x.vertex = (code 7).vertex := by
    funext b
    cases b
    · exact vs
    · exact vt
  rcases hx with ⟨hv, he, hf, hm, ha, hb, hc, hd⟩
  simp only [Bool.forall_bool, forall_fin4, forall_fin6] at he hf hb hc
  norm_num [vs, vt, Matrix.cons_val_two, Matrix.cons_val_three] at hb
  clear hv ha hs ht vs vt
  have He : x.edge = (code 7).edge := by
    simp only [funext_iff, Bool.forall_bool, forall_fin6]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec_val_five]
    repeat' constructor <;> omega
  norm_num [He, code, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, vec_val_five] at hc
  have Hf : x.face = (code 7).face := by
    simp only [funext_iff, Bool.forall_bool, forall_fin4]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three]
    repeat' constructor <;> omega
  apply Coordinates.ext Hv He Hf
  norm_num [Hf, code, Matrix.cons_val_two, Matrix.cons_val_three] at hd ⊢
  omega

lemma eq_code_8 (x : Coordinates) (hx : x.IsValid)
    (hs : x.vertex false 0 = 1) (ht : x.vertex true 3 = 1)
    (h0 : x.edge false 2 = 1) (h1 : x.edge true 2 = 1)
    : x = code 8 := by
  have vs := vertex_0 x hx false hs
  have vt := vertex_3 x hx true ht
  have Hv : x.vertex = (code 8).vertex := by
    funext b
    cases b
    · exact vs
    · exact vt
  rcases hx with ⟨hv, he, hf, hm, ha, hb, hc, hd⟩
  simp only [Bool.forall_bool, forall_fin4, forall_fin6] at he hf hb hc
  norm_num [vs, vt, Matrix.cons_val_two, Matrix.cons_val_three] at hb
  clear hv ha hs ht vs vt
  have He : x.edge = (code 8).edge := by
    simp only [funext_iff, Bool.forall_bool, forall_fin6]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec_val_five]
    repeat' constructor <;> omega
  norm_num [He, code, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, vec_val_five] at hc
  have Hf : x.face = (code 8).face := by
    simp only [funext_iff, Bool.forall_bool, forall_fin4]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three]
    repeat' constructor <;> omega
  apply Coordinates.ext Hv He Hf
  norm_num [Hf, code, Matrix.cons_val_two, Matrix.cons_val_three] at hd ⊢
  omega

lemma eq_code_9 (x : Coordinates) (hx : x.IsValid)
    (hs : x.vertex false 0 = 1) (ht : x.vertex true 3 = 1)
    (h0 : x.edge false 2 = 1) (h1 : x.edge true 1 = 1) (_h2 : x.volume ≠ 1) (h3 : x.face false 0 ≠ 1)
    : x = code 9 := by
  have vs := vertex_0 x hx false hs
  have vt := vertex_3 x hx true ht
  have Hv : x.vertex = (code 9).vertex := by
    funext b
    cases b
    · exact vs
    · exact vt
  rcases hx with ⟨hv, he, hf, hm, ha, hb, hc, hd⟩
  simp only [Bool.forall_bool, forall_fin4, forall_fin6] at he hf hb hc
  norm_num [vs, vt, Matrix.cons_val_two, Matrix.cons_val_three] at hb
  clear hv ha hs ht vs vt
  have He : x.edge = (code 9).edge := by
    simp only [funext_iff, Bool.forall_bool, forall_fin6]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec_val_five]
    repeat' constructor <;> omega
  norm_num [He, code, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, vec_val_five] at hc
  have Hf : x.face = (code 9).face := by
    simp only [funext_iff, Bool.forall_bool, forall_fin4]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three]
    repeat' constructor <;> omega
  apply Coordinates.ext Hv He Hf
  norm_num [Hf, code, Matrix.cons_val_two, Matrix.cons_val_three] at hd ⊢
  omega

lemma eq_code_10 (x : Coordinates) (hx : x.IsValid)
    (hs : x.vertex false 0 = 1) (ht : x.vertex true 3 = 1)
    (h0 : x.edge false 2 = 1) (h1 : x.edge true 1 = 1) (h2 : x.volume = 1)
    : x = code 10 := by
  have vs := vertex_0 x hx false hs
  have vt := vertex_3 x hx true ht
  have Hv : x.vertex = (code 10).vertex := by
    funext b
    cases b
    · exact vs
    · exact vt
  rcases hx with ⟨hv, he, hf, hm, ha, hb, hc, hd⟩
  simp only [Bool.forall_bool, forall_fin4, forall_fin6] at he hf hb hc
  norm_num [vs, vt, Matrix.cons_val_two, Matrix.cons_val_three] at hb
  clear hv ha hs ht vs vt
  have He : x.edge = (code 10).edge := by
    simp only [funext_iff, Bool.forall_bool, forall_fin6]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec_val_five]
    repeat' constructor <;> omega
  norm_num [He, code, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, vec_val_five] at hc
  have Hf : x.face = (code 10).face := by
    simp only [funext_iff, Bool.forall_bool, forall_fin4]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three]
    repeat' constructor <;> omega
  apply Coordinates.ext Hv He Hf
  norm_num [Hf, code, Matrix.cons_val_two, Matrix.cons_val_three] at hd ⊢
  omega

lemma eq_code_11 (x : Coordinates) (hx : x.IsValid)
    (hs : x.vertex false 0 = 1) (ht : x.vertex true 3 = 1)
    (h0 : x.edge false 2 = 1) (h1 : x.edge true 1 = 1) (h2 : x.volume ≠ 1) (h3 : x.face false 0 = 1)
    : x = code 11 := by
  have vs := vertex_0 x hx false hs
  have vt := vertex_3 x hx true ht
  have Hv : x.vertex = (code 11).vertex := by
    funext b
    cases b
    · exact vs
    · exact vt
  rcases hx with ⟨hv, he, hf, hm, ha, hb, hc, hd⟩
  simp only [Bool.forall_bool, forall_fin4, forall_fin6] at he hf hb hc
  norm_num [vs, vt, Matrix.cons_val_two, Matrix.cons_val_three] at hb
  clear hv ha hs ht vs vt
  have He : x.edge = (code 11).edge := by
    simp only [funext_iff, Bool.forall_bool, forall_fin6]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec_val_five]
    repeat' constructor <;> omega
  norm_num [He, code, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, vec_val_five] at hc
  have Hf : x.face = (code 11).face := by
    simp only [funext_iff, Bool.forall_bool, forall_fin4]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three]
    repeat' constructor <;> omega
  apply Coordinates.ext Hv He Hf
  norm_num [Hf, code, Matrix.cons_val_two, Matrix.cons_val_three] at hd ⊢
  omega

lemma eq_code_12 (x : Coordinates) (hx : x.IsValid)
    (hs : x.vertex false 0 = 1) (ht : x.vertex true 3 = 1)
    (h0 : x.edge false 2 = 1) (h1 : x.edge true 0 = 1)
    : x = code 12 := by
  have vs := vertex_0 x hx false hs
  have vt := vertex_3 x hx true ht
  have Hv : x.vertex = (code 12).vertex := by
    funext b
    cases b
    · exact vs
    · exact vt
  rcases hx with ⟨hv, he, hf, hm, ha, hb, hc, hd⟩
  simp only [Bool.forall_bool, forall_fin4, forall_fin6] at he hf hb hc
  norm_num [vs, vt, Matrix.cons_val_two, Matrix.cons_val_three] at hb
  clear hv ha hs ht vs vt
  have He : x.edge = (code 12).edge := by
    simp only [funext_iff, Bool.forall_bool, forall_fin6]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec_val_five]
    repeat' constructor <;> omega
  norm_num [He, code, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, vec_val_five] at hc
  have Hf : x.face = (code 12).face := by
    simp only [funext_iff, Bool.forall_bool, forall_fin4]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three]
    repeat' constructor <;> omega
  apply Coordinates.ext Hv He Hf
  norm_num [Hf, code, Matrix.cons_val_two, Matrix.cons_val_three] at hd ⊢
  omega

lemma eq_code_13 (x : Coordinates) (hx : x.IsValid)
    (hs : x.vertex false 0 = 1) (ht : x.vertex true 3 = 1)
    (h0 : x.edge false 1 = 1)
    : x = code 13 := by
  have vs := vertex_0 x hx false hs
  have vt := vertex_3 x hx true ht
  have Hv : x.vertex = (code 13).vertex := by
    funext b
    cases b
    · exact vs
    · exact vt
  rcases hx with ⟨hv, he, hf, hm, ha, hb, hc, hd⟩
  simp only [Bool.forall_bool, forall_fin4, forall_fin6] at he hf hb hc
  norm_num [vs, vt, Matrix.cons_val_two, Matrix.cons_val_three] at hb
  clear hv ha hs ht vs vt
  have He : x.edge = (code 13).edge := by
    simp only [funext_iff, Bool.forall_bool, forall_fin6]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec_val_five]
    repeat' constructor <;> omega
  norm_num [He, code, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, vec_val_five] at hc
  have Hf : x.face = (code 13).face := by
    simp only [funext_iff, Bool.forall_bool, forall_fin4]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three]
    repeat' constructor <;> omega
  apply Coordinates.ext Hv He Hf
  norm_num [Hf, code, Matrix.cons_val_two, Matrix.cons_val_three] at hd ⊢
  omega

lemma eq_code_14 (x : Coordinates) (hx : x.IsValid)
    (hs : x.vertex false 0 = 1) (ht : x.vertex true 3 = 1)
    (h0 : x.edge false 0 = 1) (h1 : x.edge true 0 ≠ 1)
    : x = code 14 := by
  have vs := vertex_0 x hx false hs
  have vt := vertex_3 x hx true ht
  have Hv : x.vertex = (code 14).vertex := by
    funext b
    cases b
    · exact vs
    · exact vt
  rcases hx with ⟨hv, he, hf, hm, ha, hb, hc, hd⟩
  simp only [Bool.forall_bool, forall_fin4, forall_fin6] at he hf hb hc
  norm_num [vs, vt, Matrix.cons_val_two, Matrix.cons_val_three] at hb
  clear hv ha hs ht vs vt
  have He : x.edge = (code 14).edge := by
    simp only [funext_iff, Bool.forall_bool, forall_fin6]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec_val_five]
    repeat' constructor <;> omega
  norm_num [He, code, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, vec_val_five] at hc
  have Hf : x.face = (code 14).face := by
    simp only [funext_iff, Bool.forall_bool, forall_fin4]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three]
    repeat' constructor <;> omega
  apply Coordinates.ext Hv He Hf
  norm_num [Hf, code, Matrix.cons_val_two, Matrix.cons_val_three] at hd ⊢
  omega

lemma eq_code_15 (x : Coordinates) (hx : x.IsValid)
    (hs : x.vertex false 0 = 1) (ht : x.vertex true 3 = 1)
    (h0 : x.edge false 0 = 1) (h1 : x.edge true 0 = 1)
    : x = code 15 := by
  have vs := vertex_0 x hx false hs
  have vt := vertex_3 x hx true ht
  have Hv : x.vertex = (code 15).vertex := by
    funext b
    cases b
    · exact vs
    · exact vt
  rcases hx with ⟨hv, he, hf, hm, ha, hb, hc, hd⟩
  simp only [Bool.forall_bool, forall_fin4, forall_fin6] at he hf hb hc
  norm_num [vs, vt, Matrix.cons_val_two, Matrix.cons_val_three] at hb
  clear hv ha hs ht vs vt
  have He : x.edge = (code 15).edge := by
    simp only [funext_iff, Bool.forall_bool, forall_fin6]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec_val_five]
    repeat' constructor <;> omega
  norm_num [He, code, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, vec_val_five] at hc
  have Hf : x.face = (code 15).face := by
    simp only [funext_iff, Bool.forall_bool, forall_fin4]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three]
    repeat' constructor <;> omega
  apply Coordinates.ext Hv He Hf
  norm_num [Hf, code, Matrix.cons_val_two, Matrix.cons_val_three] at hd ⊢
  omega

lemma eq_code_16 (x : Coordinates) (hx : x.IsValid)
    (hs : x.vertex false 1 = 1) (ht : x.vertex true 1 = 1)
    : x = code 16 := by
  have vs := vertex_1 x hx false hs
  have vt := vertex_1 x hx true ht
  have Hv : x.vertex = (code 16).vertex := by
    funext b
    cases b
    · exact vs
    · exact vt
  rcases hx with ⟨hv, he, hf, hm, ha, hb, hc, hd⟩
  simp only [Bool.forall_bool, forall_fin4, forall_fin6] at he hf hb hc
  norm_num [vs, vt, Matrix.cons_val_two, Matrix.cons_val_three] at hb
  clear hv ha hs ht vs vt
  have He : x.edge = (code 16).edge := by
    simp only [funext_iff, Bool.forall_bool, forall_fin6]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec_val_five]
    repeat' constructor <;> omega
  norm_num [He, code, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, vec_val_five] at hc
  have Hf : x.face = (code 16).face := by
    simp only [funext_iff, Bool.forall_bool, forall_fin4]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three]
    repeat' constructor <;> omega
  apply Coordinates.ext Hv He Hf
  norm_num [Hf, code, Matrix.cons_val_two, Matrix.cons_val_three] at hd ⊢
  omega

lemma eq_code_17 (x : Coordinates) (hx : x.IsValid)
    (hs : x.vertex false 1 = 1) (ht : x.vertex true 3 = 1)
    : x = code 17 := by
  have vs := vertex_1 x hx false hs
  have vt := vertex_3 x hx true ht
  have Hv : x.vertex = (code 17).vertex := by
    funext b
    cases b
    · exact vs
    · exact vt
  rcases hx with ⟨hv, he, hf, hm, ha, hb, hc, hd⟩
  simp only [Bool.forall_bool, forall_fin4, forall_fin6] at he hf hb hc
  norm_num [vs, vt, Matrix.cons_val_two, Matrix.cons_val_three] at hb
  clear hv ha hs ht vs vt
  have He : x.edge = (code 17).edge := by
    simp only [funext_iff, Bool.forall_bool, forall_fin6]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec_val_five]
    repeat' constructor <;> omega
  norm_num [He, code, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, vec_val_five] at hc
  have Hf : x.face = (code 17).face := by
    simp only [funext_iff, Bool.forall_bool, forall_fin4]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three]
    repeat' constructor <;> omega
  apply Coordinates.ext Hv He Hf
  norm_num [Hf, code, Matrix.cons_val_two, Matrix.cons_val_three] at hd ⊢
  omega

lemma eq_code_18 (x : Coordinates) (hx : x.IsValid)
    (hs : x.vertex false 2 = 1) (ht : x.vertex true 2 = 1)
    : x = code 18 := by
  have vs := vertex_2 x hx false hs
  have vt := vertex_2 x hx true ht
  have Hv : x.vertex = (code 18).vertex := by
    funext b
    cases b
    · exact vs
    · exact vt
  rcases hx with ⟨hv, he, hf, hm, ha, hb, hc, hd⟩
  simp only [Bool.forall_bool, forall_fin4, forall_fin6] at he hf hb hc
  norm_num [vs, vt, Matrix.cons_val_two, Matrix.cons_val_three] at hb
  clear hv ha hs ht vs vt
  have He : x.edge = (code 18).edge := by
    simp only [funext_iff, Bool.forall_bool, forall_fin6]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec_val_five]
    repeat' constructor <;> omega
  norm_num [He, code, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, vec_val_five] at hc
  have Hf : x.face = (code 18).face := by
    simp only [funext_iff, Bool.forall_bool, forall_fin4]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three]
    repeat' constructor <;> omega
  apply Coordinates.ext Hv He Hf
  norm_num [Hf, code, Matrix.cons_val_two, Matrix.cons_val_three] at hd ⊢
  omega

lemma eq_code_19 (x : Coordinates) (hx : x.IsValid)
    (hs : x.vertex false 2 = 1) (ht : x.vertex true 3 = 1)
    (h0 : x.edge false 2 = 0)
    : x = code 19 := by
  have vs := vertex_2 x hx false hs
  have vt := vertex_3 x hx true ht
  have Hv : x.vertex = (code 19).vertex := by
    funext b
    cases b
    · exact vs
    · exact vt
  rcases hx with ⟨hv, he, hf, hm, ha, hb, hc, hd⟩
  simp only [Bool.forall_bool, forall_fin4, forall_fin6] at he hf hb hc
  norm_num [vs, vt, Matrix.cons_val_two, Matrix.cons_val_three] at hb
  clear hv ha hs ht vs vt
  have He : x.edge = (code 19).edge := by
    simp only [funext_iff, Bool.forall_bool, forall_fin6]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec_val_five]
    repeat' constructor <;> omega
  norm_num [He, code, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, vec_val_five] at hc
  have Hf : x.face = (code 19).face := by
    simp only [funext_iff, Bool.forall_bool, forall_fin4]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three]
    repeat' constructor <;> omega
  apply Coordinates.ext Hv He Hf
  norm_num [Hf, code, Matrix.cons_val_two, Matrix.cons_val_three] at hd ⊢
  omega

lemma eq_code_20 (x : Coordinates) (hx : x.IsValid)
    (hs : x.vertex false 2 = 1) (ht : x.vertex true 3 = 1)
    (_h0 : x.edge false 2 ≠ 0) (h1 : x.face false 1 ≠ 0)
    : x = code 20 := by
  have vs := vertex_2 x hx false hs
  have vt := vertex_3 x hx true ht
  have Hv : x.vertex = (code 20).vertex := by
    funext b
    cases b
    · exact vs
    · exact vt
  rcases hx with ⟨hv, he, hf, hm, ha, hb, hc, hd⟩
  simp only [Bool.forall_bool, forall_fin4, forall_fin6] at he hf hb hc
  norm_num [vs, vt, Matrix.cons_val_two, Matrix.cons_val_three] at hb
  clear hv ha hs ht vs vt
  have He : x.edge = (code 20).edge := by
    simp only [funext_iff, Bool.forall_bool, forall_fin6]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec_val_five]
    repeat' constructor <;> omega
  norm_num [He, code, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, vec_val_five] at hc
  have Hf : x.face = (code 20).face := by
    simp only [funext_iff, Bool.forall_bool, forall_fin4]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three]
    repeat' constructor <;> omega
  apply Coordinates.ext Hv He Hf
  norm_num [Hf, code, Matrix.cons_val_two, Matrix.cons_val_three] at hd ⊢
  omega

lemma eq_code_21 (x : Coordinates) (hx : x.IsValid)
    (hs : x.vertex false 2 = 1) (ht : x.vertex true 3 = 1)
    (h0 : x.edge false 2 ≠ 0) (h1 : x.face false 1 = 0)
    : x = code 21 := by
  have vs := vertex_2 x hx false hs
  have vt := vertex_3 x hx true ht
  have Hv : x.vertex = (code 21).vertex := by
    funext b
    cases b
    · exact vs
    · exact vt
  rcases hx with ⟨hv, he, hf, hm, ha, hb, hc, hd⟩
  simp only [Bool.forall_bool, forall_fin4, forall_fin6] at he hf hb hc
  norm_num [vs, vt, Matrix.cons_val_two, Matrix.cons_val_three] at hb
  clear hv ha hs ht vs vt
  have He : x.edge = (code 21).edge := by
    simp only [funext_iff, Bool.forall_bool, forall_fin6]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec_val_five]
    repeat' constructor <;> omega
  norm_num [He, code, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, vec_val_five] at hc
  have Hf : x.face = (code 21).face := by
    simp only [funext_iff, Bool.forall_bool, forall_fin4]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three]
    repeat' constructor <;> omega
  apply Coordinates.ext Hv He Hf
  norm_num [Hf, code, Matrix.cons_val_two, Matrix.cons_val_three] at hd ⊢
  omega

lemma eq_code_22 (x : Coordinates) (hx : x.IsValid)
    (hs : x.vertex false 3 = 1) (ht : x.vertex true 3 = 1)
    : x = code 22 := by
  have vs := vertex_3 x hx false hs
  have vt := vertex_3 x hx true ht
  have Hv : x.vertex = (code 22).vertex := by
    funext b
    cases b
    · exact vs
    · exact vt
  rcases hx with ⟨hv, he, hf, hm, ha, hb, hc, hd⟩
  simp only [Bool.forall_bool, forall_fin4, forall_fin6] at he hf hb hc
  norm_num [vs, vt, Matrix.cons_val_two, Matrix.cons_val_three] at hb
  clear hv ha hs ht vs vt
  have He : x.edge = (code 22).edge := by
    simp only [funext_iff, Bool.forall_bool, forall_fin6]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec_val_five]
    repeat' constructor <;> omega
  norm_num [He, code, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, vec_val_five] at hc
  have Hf : x.face = (code 22).face := by
    simp only [funext_iff, Bool.forall_bool, forall_fin4]
    norm_num [code, Matrix.cons_val_two, Matrix.cons_val_three]
    repeat' constructor <;> omega
  apply Coordinates.ext Hv He Hf
  norm_num [Hf, code, Matrix.cons_val_two, Matrix.cons_val_three] at hd ⊢
  omega

lemma impossible_10 (x : Coordinates) (hx : x.IsValid)
    (hs : x.vertex false 1 = 1) (ht : x.vertex true 0 = 1) : False := by
  rcases hx with ⟨hv, he, hf, hm, ha, hb, hc, hd⟩
  simp only [Bool.forall_bool, forall_fin4, forall_fin6] at hv he hf ha hb hc
  omega

lemma impossible_12 (x : Coordinates) (hx : x.IsValid)
    (hs : x.vertex false 1 = 1) (ht : x.vertex true 2 = 1) : False := by
  rcases hx with ⟨hv, he, hf, hm, ha, hb, hc, hd⟩
  simp only [Bool.forall_bool, forall_fin4, forall_fin6] at hv he hf ha hb hc
  omega

lemma impossible_20 (x : Coordinates) (hx : x.IsValid)
    (hs : x.vertex false 2 = 1) (ht : x.vertex true 0 = 1) : False := by
  rcases hx with ⟨hv, he, hf, hm, ha, hb, hc, hd⟩
  simp only [Bool.forall_bool, forall_fin4, forall_fin6] at hv he hf ha hb hc
  omega

lemma impossible_21 (x : Coordinates) (hx : x.IsValid)
    (hs : x.vertex false 2 = 1) (ht : x.vertex true 1 = 1) : False := by
  rcases hx with ⟨hv, he, hf, hm, ha, hb, hc, hd⟩
  simp only [Bool.forall_bool, forall_fin4, forall_fin6] at hv he hf ha hb hc
  omega

lemma impossible_30 (x : Coordinates) (hx : x.IsValid)
    (hs : x.vertex false 3 = 1) (ht : x.vertex true 0 = 1) : False := by
  rcases hx with ⟨hv, he, hf, hm, ha, hb, hc, hd⟩
  simp only [Bool.forall_bool, forall_fin4, forall_fin6] at hv he hf ha hb hc
  omega

lemma impossible_31 (x : Coordinates) (hx : x.IsValid)
    (hs : x.vertex false 3 = 1) (ht : x.vertex true 1 = 1) : False := by
  rcases hx with ⟨hv, he, hf, hm, ha, hb, hc, hd⟩
  simp only [Bool.forall_bool, forall_fin4, forall_fin6] at hv he hf ha hb hc
  omega

lemma impossible_32 (x : Coordinates) (hx : x.IsValid)
    (hs : x.vertex false 3 = 1) (ht : x.vertex true 2 = 1) : False := by
  rcases hx with ⟨hv, he, hf, hm, ha, hb, hc, hd⟩
  simp only [Bool.forall_bool, forall_fin4, forall_fin6] at hv he hf ha hb hc
  omega

lemma cases_01 (x : Coordinates) (hx : x.IsValid)
    (hs : x.vertex false 0 = 1) (ht : x.vertex true 1 = 1) :
    ∃ i : Fin 23, x = code i := by
  by_cases h0 : x.edge false 0 = 0
  · exact ⟨1, eq_code_1 x hx hs ht h0⟩
  by_cases h1 : x.face false 0 = 0
  · exact ⟨3, eq_code_3 x hx hs ht h0 h1⟩
  · exact ⟨2, eq_code_2 x hx hs ht h0 h1⟩

lemma four_paths (x : Coordinates) (hx : x.IsValid)
    (hs : x.vertex false 0 = 1) (ht : x.vertex true 3 = 1) (b : Bool) :
    x.edge b 0 = 1 ∨ x.edge b 1 = 1 ∨ x.edge b 2 = 1 ∨ x.edge b 3 = 1 := by
  rcases hx with ⟨hv, he, hf, hm, ha, hb, hc, hd⟩
  have hn := he b
  have hb := hb b
  simp only [Bool.forall_bool, forall_fin4, forall_fin6] at hv hn ha
  omega

lemma cases_03 (x : Coordinates) (hx : x.IsValid)
    (hs : x.vertex false 0 = 1) (ht : x.vertex true 3 = 1) :
    ∃ i : Fin 23, x = code i := by
  rcases four_paths x hx hs ht false with h0 | h0 | h0 | h0
  · by_cases h1 : x.edge true 0 = 1
    · exact ⟨15, eq_code_15 x hx hs ht h0 h1⟩
    · exact ⟨14, eq_code_14 x hx hs ht h0 h1⟩
  · exact ⟨13, eq_code_13 x hx hs ht h0⟩
  · rcases four_paths x hx hs ht true with h1 | h1 | h1 | h1
    · exact ⟨12, eq_code_12 x hx hs ht h0 h1⟩
    · by_cases h2 : x.volume = 1
      · exact ⟨10, eq_code_10 x hx hs ht h0 h1 h2⟩
      by_cases h3 : x.face false 0 = 1
      · exact ⟨11, eq_code_11 x hx hs ht h0 h1 h2 h3⟩
      · exact ⟨9, eq_code_9 x hx hs ht h0 h1 h2 h3⟩
    · exact ⟨8, eq_code_8 x hx hs ht h0 h1⟩
    · exact ⟨7, eq_code_7 x hx hs ht h0 h1⟩
  · by_cases h1 : x.face false 3 = 0
    · exact ⟨5, eq_code_5 x hx hs ht h0 h1⟩
    · exact ⟨6, eq_code_6 x hx hs ht h0 h1⟩

lemma cases_23 (x : Coordinates) (hx : x.IsValid)
    (hs : x.vertex false 2 = 1) (ht : x.vertex true 3 = 1) :
    ∃ i : Fin 23, x = code i := by
  by_cases h0 : x.edge false 2 = 0
  · exact ⟨19, eq_code_19 x hx hs ht h0⟩
  by_cases h1 : x.face false 1 = 0
  · exact ⟨21, eq_code_21 x hx hs ht h0 h1⟩
  · exact ⟨20, eq_code_20 x hx hs ht h0 h1⟩

lemma has_vertex (x : Coordinates) (hx : x.IsValid) (b : Bool) :
    x.vertex b 0 = 1 ∨ x.vertex b 1 = 1 ∨ x.vertex b 2 = 1 ∨ x.vertex b 3 = 1 := by
  have hp := hx.1 b
  have ha := hx.2.2.2.2.1 b
  simp only [forall_fin4] at hp
  omega

lemma is_code (x : Coordinates) (hx : x.IsValid) : ∃ i : Fin 23, x = code i := by
  rcases has_vertex x hx false with hs | hs | hs | hs <;>
    rcases has_vertex x hx true with ht | ht | ht | ht
  · exact ⟨0, eq_code_0 x hx hs ht⟩
  · exact cases_01 x hx hs ht
  · exact ⟨4, eq_code_4 x hx hs ht⟩
  · exact cases_03 x hx hs ht
  · exact (impossible_10 x hx hs ht).elim
  · exact ⟨16, eq_code_16 x hx hs ht⟩
  · exact (impossible_12 x hx hs ht).elim
  · exact ⟨17, eq_code_17 x hx hs ht⟩
  · exact (impossible_20 x hx hs ht).elim
  · exact (impossible_21 x hx hs ht).elim
  · exact ⟨18, eq_code_18 x hx hs ht⟩
  · exact cases_23 x hx hs ht
  · exact (impossible_30 x hx hs ht).elim
  · exact (impossible_31 x hx hs ht).elim
  · exact (impossible_32 x hx hs ht).elim
  · exact ⟨22, eq_code_22 x hx hs ht⟩

end Thomason.GrayTwo

end

end OAI
